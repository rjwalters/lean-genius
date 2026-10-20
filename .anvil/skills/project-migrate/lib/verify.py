"""Post-apply verification for `anvil:project-migrate` (issue #297).

After ``apply_plan`` runs, this module walks the resulting project tree
and confirms the migration produced a fully-migrated shape. The contract:

1. ``<project>/BRIEF.md`` parses with at least one document.
2. Every slug listed in BRIEF has a corresponding ``<project>/<slug>/``
   directory containing at least one ``<slug>.N/`` version dir.
3. Every version dir's body filename is ``<slug>.md`` (or the dir is empty).
4. No ``.anvil.json`` files remain anywhere in the project tree.
5. No ``memo.md`` / ``proposal.md`` / etc. skill-fixed bodies remain.
6. No ``memo.N/`` version dirs sit directly at the project root.

Used by the command spec's "Verify" step to produce a final pass/fail
report after ``--apply``. Can also be invoked standalone to audit any
project against the canonical shape contract.

Design notes
------------

- **Read-only.** Like detection and planning, verify reads but never writes.
- **Granular results.** Returns a typed :class:`VerifyResult` with separate
  fields per check so the caller can format a useful report (rather than a
  single bool).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List

from .detect import (
    ANVIL_JSON_FILENAME,
    _SKILL_FIXED_BODY_FILENAMES,
    inventory_project,
)


_VERSION_DIR_RE = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")


@dataclass
class VerifyResult:
    """Typed result of :func:`verify_migration`.

    Attributes
    ----------
    project_dir
        Project root that was verified.
    brief_parses
        True iff ``<project>/BRIEF.md`` exists and parses with a non-empty
        documents list.
    discovered_slugs
        Slugs discovered on disk (from inventory walk).
    brief_slugs
        Slugs listed in the project BRIEF.
    orphaned_threads
        Slugs with on-disk threads but no BRIEF entry.
    missing_threads
        Slugs in BRIEF with no on-disk thread.
    stale_anvil_jsons
        Paths to ``.anvil.json`` files that remained after apply.
    stale_skill_fixed_bodies
        Paths to body files with skill-fixed names (e.g., ``memo.md``).
    root_version_dirs
        Paths to version dirs sitting directly at the project root (should
        be zero).
    ok
        True iff every check passed.
    """

    project_dir: Path
    brief_parses: bool = False
    discovered_slugs: List[str] = field(default_factory=list)
    brief_slugs: List[str] = field(default_factory=list)
    orphaned_threads: List[str] = field(default_factory=list)
    missing_threads: List[str] = field(default_factory=list)
    stale_anvil_jsons: List[Path] = field(default_factory=list)
    stale_skill_fixed_bodies: List[Path] = field(default_factory=list)
    root_version_dirs: List[Path] = field(default_factory=list)
    ok: bool = False

    def to_report(self) -> str:
        """Return a markdown report of the verification result."""
        lines: List[str] = []
        lines.append(f"# Migration verification: {self.project_dir.name}")
        lines.append("")
        lines.append(f"- BRIEF parses: {'OK' if self.brief_parses else 'FAIL'}")
        lines.append(
            f"- Discovered slugs ({len(self.discovered_slugs)}): "
            f"{', '.join(self.discovered_slugs) or '(none)'}"
        )
        lines.append(
            f"- BRIEF slugs ({len(self.brief_slugs)}): "
            f"{', '.join(self.brief_slugs) or '(none)'}"
        )
        if self.orphaned_threads:
            lines.append(
                f"- Orphaned threads (on disk, not in BRIEF): "
                f"{', '.join(self.orphaned_threads)}"
            )
        if self.missing_threads:
            lines.append(
                f"- Missing threads (in BRIEF, not on disk): "
                f"{', '.join(self.missing_threads)}"
            )
        if self.stale_anvil_jsons:
            lines.append(
                f"- Stale .anvil.json files ({len(self.stale_anvil_jsons)}): "
                + ", ".join(str(p) for p in self.stale_anvil_jsons)
            )
        if self.stale_skill_fixed_bodies:
            lines.append(
                f"- Stale skill-fixed bodies ({len(self.stale_skill_fixed_bodies)}): "
                + ", ".join(str(p) for p in self.stale_skill_fixed_bodies)
            )
        if self.root_version_dirs:
            lines.append(
                f"- Version dirs at project root ({len(self.root_version_dirs)}): "
                + ", ".join(str(p) for p in self.root_version_dirs)
            )
        lines.append("")
        lines.append(f"**Overall**: {'PASS' if self.ok else 'FAIL'}")
        return "\n".join(lines) + "\n"


def _walk_for_anvil_jsons(project_dir: Path) -> List[Path]:
    """Walk ``project_dir`` recursively and return every `.anvil.json` found."""
    out: List[Path] = []
    if not project_dir.is_dir():
        return out
    for path in sorted(project_dir.rglob(ANVIL_JSON_FILENAME)):
        # Skip rollback snapshots.
        if any(part == ".anvil-migrate-rollback" for part in path.parts):
            continue
        out.append(path)
    return out


def _walk_for_skill_fixed_bodies(project_dir: Path) -> List[Path]:
    """Walk ``project_dir`` and return every skill-fixed body filename found."""
    out: List[Path] = []
    if not project_dir.is_dir():
        return out
    for name in _SKILL_FIXED_BODY_FILENAMES:
        for path in sorted(project_dir.rglob(name)):
            if any(part == ".anvil-migrate-rollback" for part in path.parts):
                continue
            if any(part.startswith(".") for part in path.parts[
                len(project_dir.parts):
            ]):
                continue
            out.append(path)
    return out


def _find_root_version_dirs(project_dir: Path) -> List[Path]:
    """Return any `<stem>.<N>/` dirs directly at the project root."""
    if not project_dir.is_dir():
        return []
    out: List[Path] = []
    try:
        for child in project_dir.iterdir():
            if not child.is_dir():
                continue
            if child.name.startswith("."):
                continue
            if _VERSION_DIR_RE.match(child.name) is not None:
                out.append(child)
    except OSError:
        return out
    return sorted(out)


def verify_migration(project_dir: Path) -> VerifyResult:
    """Verify that ``project_dir`` is in the fully-migrated shape.

    Returns a :class:`VerifyResult` with the granular check outcomes.
    """
    project_dir = Path(project_dir).resolve()
    result = VerifyResult(project_dir=project_dir)

    # Build the inventory; this gives us the discovered threads.
    inv = inventory_project(project_dir)
    result.brief_parses = inv.has_project_brief

    if inv.has_project_brief:
        from .detect import _project_brief_slugs
        result.brief_slugs = _project_brief_slugs(project_dir)

    discovered = [t.slug for t in inv.threads]
    result.discovered_slugs = sorted(set(discovered))

    # Orphaned: on disk but not in BRIEF.
    if inv.has_project_brief:
        brief_set = set(result.brief_slugs)
        result.orphaned_threads = sorted(
            s for s in result.discovered_slugs if s not in brief_set
        )
        result.missing_threads = sorted(
            s for s in result.brief_slugs if s not in result.discovered_slugs
        )

    # Stale `.anvil.json` files (must be zero post-migration).
    result.stale_anvil_jsons = _walk_for_anvil_jsons(project_dir)

    # Stale skill-fixed body files (must be zero post-migration).
    result.stale_skill_fixed_bodies = _walk_for_skill_fixed_bodies(project_dir)

    # Version dirs at the project root (must be zero post-migration).
    result.root_version_dirs = _find_root_version_dirs(project_dir)

    # Overall pass: every check clean.
    result.ok = (
        result.brief_parses
        and not result.stale_anvil_jsons
        and not result.stale_skill_fixed_bodies
        and not result.root_version_dirs
        and not result.orphaned_threads
    )
    return result


__all__ = [
    "VerifyResult",
    "verify_migration",
]
