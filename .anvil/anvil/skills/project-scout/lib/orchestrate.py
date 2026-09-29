"""Single-entry orchestration for `anvil:project-scout` (issue #407).

``run(root, ...)`` composes ``walk → cluster → report`` and returns a
:class:`ScoutResult`. The scan itself is **strictly read-only** — the
only writes anywhere in the skill are the operator-requested ``--report``
/ ``--json`` output paths handled here, and the operator contract
(``commands/project-scout.md``) directs those OUTSIDE the scanned tree
(or accepts that a report inside the tree is an operator-requested
write, not a scout mutation).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, Sequence

from .cluster import Classification, classify_tree
from .report import build_json, render_markdown
from .walk import WalkResult, walk_tree


@dataclass
class ScoutResult:
    success: bool
    markdown: str
    data: dict
    walk: WalkResult
    classification: Classification
    warnings: list = field(default_factory=list)


def run(
    root: Path,
    include: Sequence[str] = (),
    exclude: Sequence[str] = (),
    verbose: bool = False,
    report_path: Optional[Path] = None,
    json_path: Optional[Path] = None,
) -> ScoutResult:
    """Scan ``root`` and build the classified adoption report.

    Returns a :class:`ScoutResult` whose ``markdown`` / ``data`` carry
    the two report surfaces. ``success`` is False when the coverage
    identity is violated (a scout bug, surfaced loudly rather than
    silently dropping files) or the root does not exist.
    """
    root = Path(root).resolve()
    warnings: list = []

    wr = walk_tree(root, include=include, exclude=exclude)
    cls = classify_tree(wr)
    markdown = render_markdown(wr, cls, verbose=verbose)
    data = build_json(wr, cls, verbose=verbose)

    success = root.is_dir() and cls.coverage.identity_holds
    if not root.is_dir():
        warnings.append(f"root {root} is not a directory")
    if not cls.coverage.identity_holds:
        warnings.append(
            "coverage identity violated — this is a scout bug; "
            "file an issue with the JSON sidecar attached"
        )

    # Operator-requested report writes — the ONLY writes in this skill.
    if report_path is not None:
        Path(report_path).write_text(markdown, encoding="utf-8")
    if json_path is not None:
        Path(json_path).write_text(
            json.dumps(data, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    return ScoutResult(
        success=success,
        markdown=markdown,
        data=data,
        walk=wr,
        classification=cls,
        warnings=warnings,
    )


__all__ = ["ScoutResult", "run"]
