"""Pruned repo walk + evidence collection for `anvil:project-scout` (issue #407).

Single top-down :func:`os.walk` pass with pruning. Collects four evidence
streams in one traversal:

(a) **family sites** — ``(parent_dir, stem)`` pairs where ``parent_dir``
    has at least one ``<stem>.<N>`` child (the promoted
    ``anvil/lib/project_detect.py::_VERSION_DIR_RE`` grammar), plus the
    sibling sidecar dir names (``<stem>.<N>.<tag>``) the foreign guard
    inspects;
(b) **BRIEF sites** — directories whose ``BRIEF.md`` parses as a project
    BRIEF (``project_detect._has_project_brief``);
(c) **``.anvil.json`` sites**;
(d) **candidate files** — loose ``.md`` / ``.tex`` files (subject to the
    ``--include`` positive filter).

Honest-coverage rule: every pruned subtree (dotdir, default exclude, or
operator ``--exclude`` glob) is recorded with its reason — defaults do not
get a silence pass.

Strictly read-only: this module never writes.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from fnmatch import fnmatch
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from anvil.lib.project_detect import _VERSION_DIR_RE, _has_project_brief


# Default-excluded directory names. `.git` / `.anvil` / `.loom` / `.claude`
# are also dotdirs (the walk skips dotdirs regardless — detect.py
# precedent) but are listed explicitly so their prune reason reads
# "default-exclude" rather than the generic "dotdir". `SHARE` is the
# project-share output dir; `build` is also a project-infrastructure dir
# (`project_detect._INFRASTRUCTURE_DIRS`) — pruning it globally is
# consistent with it being claimed inside clusters.
DEFAULT_EXCLUDES: Tuple[str, ...] = (
    ".git",
    "node_modules",
    ".anvil",
    ".loom",
    ".claude",
    ".venv",
    "venv",
    "__pycache__",
    "dist",
    "build",
    "target",
    "out",
    "SHARE",
)

# Candidate document extensions (mirrors enroll's `_ENROLLABLE_SUFFIXES`).
CANDIDATE_SUFFIXES: Tuple[str, ...] = (".md", ".tex")

# Prune reasons (stable strings — they appear in the JSON sidecar).
REASON_DOTDIR = "dotdir"
REASON_DEFAULT_EXCLUDE = "default-exclude"
REASON_EXCLUDE_GLOB = "exclude-glob"


@dataclass
class FamilySite:
    """One version-dir family observed at one directory.

    ``sidecar_dir_names`` are sibling dirs named ``<stem>.<N>.<tag>`` —
    the surface the foreign-grammar guard inspects for versioned tags
    (``.review-v2`` / ``.audit-v2``).
    """

    parent_dir: Path
    stem: str
    version_dir_names: List[str] = field(default_factory=list)
    sidecar_dir_names: List[str] = field(default_factory=list)

    @property
    def version_numbers(self) -> List[int]:
        out: List[int] = []
        for name in self.version_dir_names:
            m = _VERSION_DIR_RE.match(name)
            if m is not None and m.group("stem") == self.stem:
                out.append(int(m.group("num")))
        return sorted(out)


@dataclass
class PrunedSubtree:
    path: Path
    reason: str


@dataclass
class WalkResult:
    root: Path
    family_sites: List[FamilySite] = field(default_factory=list)
    brief_sites: List[Path] = field(default_factory=list)
    anvil_json_sites: List[Path] = field(default_factory=list)
    candidate_files: List[Path] = field(default_factory=list)
    pruned_subtrees: List[PrunedSubtree] = field(default_factory=list)
    dirs_scanned: int = 0
    include: Tuple[str, ...] = ()
    exclude: Tuple[str, ...] = ()


def _matches_any(rel_posix: str, name: str, globs: Sequence[str]) -> bool:
    """True iff the relative path or the basename matches any glob."""
    for pat in globs:
        if fnmatch(rel_posix, pat) or fnmatch(name, pat):
            return True
        # Convenience: `docs/` style patterns (trailing slash) match dirs.
        if pat.endswith("/") and (
            fnmatch(rel_posix, pat[:-1]) or fnmatch(name, pat[:-1])
        ):
            return True
    return False


def _prune_reason(
    name: str, rel_posix: str, exclude: Sequence[str]
) -> str:
    """Return a prune reason for a directory, or ``""`` to keep it."""
    if name in DEFAULT_EXCLUDES:
        return REASON_DEFAULT_EXCLUDE
    if name.startswith("."):
        return REASON_DOTDIR
    if _matches_any(rel_posix, name, exclude):
        return REASON_EXCLUDE_GLOB
    return ""


def _sidecar_re(stem: str) -> "re.Pattern[str]":
    return re.compile(
        r"^" + re.escape(stem) + r"\.(?P<num>\d+)\.(?P<tag>.+)$"
    )


def walk_tree(
    root: Path,
    include: Sequence[str] = (),
    exclude: Sequence[str] = (),
) -> WalkResult:
    """Walk ``root`` once, pruning + collecting evidence.

    ``include`` is a positive filter on **candidate files** only (when
    non-empty, a loose ``.md``/``.tex`` file must match at least one
    include glob to be considered). Cluster evidence (family sites /
    BRIEF sites / ``.anvil.json`` sites) is never include-filtered —
    a cluster the operator scoped out of file consideration is still
    honest-coverage-visible.

    ``exclude`` globs prune whole subtrees (matched against the
    root-relative posix path or the directory basename); every prune is
    recorded.
    """
    root = Path(root).resolve()
    result = WalkResult(
        root=root, include=tuple(include), exclude=tuple(exclude)
    )
    if not root.is_dir():
        return result

    for dirpath, dirnames, filenames in os.walk(root):
        cur = Path(dirpath)
        result.dirs_scanned += 1

        # ---- prune subtrees (recorded, never silent) -------------------
        kept: List[str] = []
        for d in sorted(dirnames):
            child = cur / d
            rel = child.relative_to(root).as_posix()
            reason = _prune_reason(d, rel, exclude)
            if reason:
                result.pruned_subtrees.append(
                    PrunedSubtree(path=child, reason=reason)
                )
            else:
                kept.append(d)
        dirnames[:] = kept

        # ---- evidence: version-dir families + sidecars -----------------
        groups: Dict[str, List[str]] = {}
        for d in kept:
            m = _VERSION_DIR_RE.match(d)
            if m is not None:
                groups.setdefault(m.group("stem"), []).append(d)
        for stem in sorted(groups):
            sidecar_re = _sidecar_re(stem)
            sidecars = sorted(
                d for d in kept if sidecar_re.match(d) is not None
            )
            result.family_sites.append(
                FamilySite(
                    parent_dir=cur,
                    stem=stem,
                    version_dir_names=sorted(
                        groups[stem],
                        key=lambda n: int(
                            _VERSION_DIR_RE.match(n).group("num")
                        ),
                    ),
                    sidecar_dir_names=sidecars,
                )
            )

        # ---- evidence: BRIEF + .anvil.json sites -----------------------
        if "BRIEF.md" in filenames and _has_project_brief(cur):
            result.brief_sites.append(cur)
        if ".anvil.json" in filenames:
            result.anvil_json_sites.append(cur)

        # ---- candidate files -------------------------------------------
        for fn in sorted(filenames):
            if not fn.endswith(CANDIDATE_SUFFIXES):
                continue
            f = cur / fn
            if include:
                rel = f.relative_to(root).as_posix()
                if not _matches_any(rel, fn, include):
                    continue
            result.candidate_files.append(f)

    # Deterministic ordering for downstream consumers + golden tests.
    result.family_sites.sort(key=lambda s: (str(s.parent_dir), s.stem))
    result.brief_sites.sort()
    result.anvil_json_sites.sort()
    result.candidate_files.sort()
    result.pruned_subtrees.sort(key=lambda p: str(p.path))
    return result


__all__ = [
    "CANDIDATE_SUFFIXES",
    "DEFAULT_EXCLUDES",
    "FamilySite",
    "PrunedSubtree",
    "REASON_DEFAULT_EXCLUDE",
    "REASON_DOTDIR",
    "REASON_EXCLUDE_GLOB",
    "WalkResult",
    "walk_tree",
]
