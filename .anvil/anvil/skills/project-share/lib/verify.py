"""Post-apply verification for `anvil:project-share` (issue #396).

Checks the written out dir against the plan:

- The ``EXPORT.md`` marker is present (the next rebuild depends on it).
- Every planned file landed at its target path.
- No stripped / structurally-excluded filename leaked into the export
  (every path component is re-checked against the strip patterns and
  the structural-exclusion set — ``BRIEF.md`` in particular).
- No critic-sibling-shaped directory (``<name>.<N>.<tag>/``) appears
  anywhere in the export tree (belt-and-suspenders: the copy source is
  only the resolved version dir, so this should be impossible by
  construction).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List

from .plan import MARKER_FILENAME, SharePlan, is_stripped

# Critic siblings are version dirs with a trailing `.<tag>`:
# `investment-memo.3.review/`, `deck.2.audit/`, etc.
_CRITIC_SIBLING_RE = re.compile(r"^.+\.\d+\.[A-Za-z][\w.-]*$")


@dataclass
class VerifyResult:
    """Outcome of :func:`verify_export`."""

    out_dir: Path
    ok: bool = True
    failures: List[str] = field(default_factory=list)
    checks_run: int = 0

    def to_report(self) -> str:
        lines = ["## Verify", ""]
        if self.ok:
            lines.append(
                f"- OK ({self.checks_run} checks): marker present, every "
                f"planned file landed, no stripped files leaked."
            )
        else:
            lines.append(f"- **FAILED** ({len(self.failures)} failures):")
            for failure in self.failures:
                lines.append(f"  - {failure}")
        lines.append("")
        return "\n".join(lines) + "\n"


def verify_export(plan: SharePlan) -> VerifyResult:
    """Verify the on-disk export matches the plan."""
    out_dir = plan.out_dir
    result = VerifyResult(out_dir=out_dir)

    def fail(msg: str) -> None:
        result.ok = False
        result.failures.append(msg)

    # 1. Marker present.
    result.checks_run += 1
    if not (out_dir / MARKER_FILENAME).is_file():
        fail(f"marker `{MARKER_FILENAME}` missing from {out_dir}")

    # 2. Every planned file landed.
    for fp in plan.all_file_plans:
        result.checks_run += 1
        target = out_dir / fp.target_rel
        if not target.is_file():
            fail(f"planned file missing from export: {fp.target_rel}")

    # 3. Per-doc dirs exist for every non-failed doc with files.
    for doc in plan.docs:
        if doc.failed or not doc.files:
            continue
        result.checks_run += 1
        if not (out_dir / doc.target_dirname).is_dir():
            fail(f"doc directory missing: {doc.target_dirname}/")

    # 4. No stripped / excluded names leaked; no critic-sibling dirs.
    if out_dir.is_dir():
        for path in sorted(out_dir.rglob("*")):
            rel = path.relative_to(out_dir)
            if rel.parts == (MARKER_FILENAME,):
                continue
            result.checks_run += 1
            if is_stripped(rel.parts, plan.config.strip):
                fail(f"stripped name leaked into export: {rel}")
            if path.is_dir() and _CRITIC_SIBLING_RE.match(path.name):
                fail(f"critic-sibling-shaped directory in export: {rel}")

    return result


__all__ = ["VerifyResult", "verify_export"]
