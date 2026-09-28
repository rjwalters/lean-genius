"""Export planning for `anvil:project-share` (issue #396).

Turns a parsed BRIEF + :class:`~.config.ExportConfig` + per-doc
collections into a typed :class:`SharePlan`:

- **Ordering**: ``export.order`` (authoritative include-list + order)
  when present, else BRIEF ``documents:`` order. Unknown slugs in
  ``order`` are a hard error naming the slug; omitted slugs are
  excluded with an informational note.
- **Strip filtering**: ``fnmatch`` of every relative path component
  against the strip patterns. Applied uniformly to version-dir
  contents, per-thread ``refs/``, and the shared ``research/`` pool.
- **Structural exclusions** (never copied, regardless of strip
  config): ``BRIEF.md`` (internal config — rubric calibrations, hard
  rules — is awkward to hand to an outside party), critic siblings
  (``<slug>.<N>.<tag>/`` are siblings of the version dir, not contents
  — the copy source is only the resolved version dir, so they are
  excluded by construction), version history (only the resolved
  version is collected), and the ``.latest`` symlink itself (the
  collector dereferences before the planner ever sees it).
- **Guard / collision checks**: the ``out`` name must not collide with
  a document slug, the shared ``research/`` / ``refs/`` dirs, or any
  thread-root-shaped directory — a blow-away rebuild aimed at a
  source-of-truth directory is refused at plan time with a clear
  error (defense-in-depth on top of the marker guard in :mod:`apply`).

The plan is pure — building it never writes to disk, which is what
makes the ``--dry-run`` flag SHA-256-verifiably side-effect-free.
"""

from __future__ import annotations

import fnmatch
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, List, Optional, Sequence, Tuple

from .collect import (
    REFS_DIRNAME,
    RESEARCH_DIRNAME,
    DocCollection,
    collect_doc,
    collect_research,
)
from .config import BRIEF_FILENAME, ExportConfig

if TYPE_CHECKING:  # pragma: no cover - typing only
    from anvil.lib.project_brief import ProjectBrief

# Marker file: its presence in the out dir is what authorizes the
# blow-away rebuild. A non-empty out dir WITHOUT this marker is a hard
# refusal (don't delete a directory that isn't ours).
MARKER_FILENAME = "EXPORT.md"

# Out-dir states reported by :func:`inspect_out_dir`.
OUT_ABSENT = "absent"
OUT_EMPTY = "empty"
OUT_MARKER = "marker"
OUT_FOREIGN = "foreign"

# Ordering-source labels recorded in EXPORT.md.
ORDERING_EXPORT_ORDER = "export.order"
ORDERING_DOCUMENTS = "documents"

# Filenames that never reach the export regardless of strip config.
STRUCTURAL_EXCLUDES = frozenset({BRIEF_FILENAME})


@dataclass
class FilePlan:
    """One file copy: absolute ``source`` → ``target_rel`` under the out dir."""

    source: Path
    target_rel: Path


@dataclass
class DocPlan:
    """Planned export of one document thread."""

    slug: str
    ordinal: int
    target_dirname: str
    collection: DocCollection
    files: List[FilePlan] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)

    @property
    def failed(self) -> bool:
        return self.collection.failed

    @property
    def failure(self) -> Optional[str]:
        return self.collection.failure


@dataclass
class SharePlan:
    """The full export plan for one project."""

    project_dir: Path
    project_name: str
    config: ExportConfig
    out_dir: Path
    ordering_source: str
    docs: List[DocPlan] = field(default_factory=list)
    excluded_slugs: List[str] = field(default_factory=list)
    research_files: List[FilePlan] = field(default_factory=list)
    cover_file: Optional[FilePlan] = None
    notes: List[str] = field(default_factory=list)

    @property
    def failed_docs(self) -> List[DocPlan]:
        return [d for d in self.docs if d.failed]

    @property
    def all_file_plans(self) -> List[FilePlan]:
        out: List[FilePlan] = []
        for doc in self.docs:
            out.extend(doc.files)
        out.extend(self.research_files)
        if self.cover_file is not None:
            out.append(self.cover_file)
        return out


def is_stripped(rel_parts: Sequence[str], patterns: Sequence[str]) -> bool:
    """True when any path component is structurally excluded or matches
    a strip pattern (``fnmatch`` per component, so a matching directory
    name excludes its whole subtree)."""
    for part in rel_parts:
        if part in STRUCTURAL_EXCLUDES:
            return True
        for pat in patterns:
            if fnmatch.fnmatch(part, pat):
                return True
    return False


def inspect_out_dir(out_dir: Path) -> str:
    """Classify the out dir for the marker guard.

    Returns one of :data:`OUT_ABSENT`, :data:`OUT_EMPTY`,
    :data:`OUT_MARKER` (previous export — safe to rebuild), or
    :data:`OUT_FOREIGN` (non-empty without the marker — refuse).
    """
    out_dir = Path(out_dir)
    if not out_dir.exists():
        return OUT_ABSENT
    if not out_dir.is_dir():
        return OUT_FOREIGN
    try:
        children = list(out_dir.iterdir())
    except OSError:
        return OUT_FOREIGN
    if not children:
        return OUT_EMPTY
    if (out_dir / MARKER_FILENAME).is_file():
        return OUT_MARKER
    return OUT_FOREIGN


def _manifest_for_tree(
    source_root: Path,
    target_root: Path,
    strip: Sequence[str],
    *,
    top_level_only: bool = False,
) -> List[FilePlan]:
    """Build the strip-filtered copy manifest for one source tree."""
    files: List[FilePlan] = []
    for path in sorted(source_root.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(source_root)
        if is_stripped(rel.parts, strip):
            continue
        if top_level_only and len(rel.parts) > 1:
            continue
        files.append(FilePlan(source=path, target_rel=target_root / rel))
    return files


def _resolve_ordering(
    brief: "ProjectBrief", config: ExportConfig
) -> Tuple[List[str], List[str], str]:
    """Apply ``export.order`` semantics.

    Returns ``(ordered_slugs, excluded_slugs, ordering_source)``.

    Raises
    ------
    ValueError
        When ``export.order`` names a slug that does not appear in the
        BRIEF ``documents:`` list (hard error naming the slug).
    """
    brief_slugs = [doc.slug for doc in brief.documents]
    if config.order is None:
        return list(brief_slugs), [], ORDERING_DOCUMENTS

    known = set(brief_slugs)
    unknown = [s for s in config.order if s not in known]
    if unknown:
        raise ValueError(
            f"export.order names slugs that do not appear in "
            f"BRIEF.documents: {unknown}. Suggested fix: remove the "
            f"unknown entries or add matching `documents:` entries."
        )
    ordered = list(config.order)
    excluded = [s for s in brief_slugs if s not in set(ordered)]
    return ordered, excluded, ORDERING_EXPORT_ORDER


def _check_out_collisions(
    project_dir: Path, brief: "ProjectBrief", config: ExportConfig
) -> None:
    """Refuse out-dir names that point at source-of-truth directories."""
    reserved = {doc.slug for doc in brief.documents}
    reserved.update({RESEARCH_DIRNAME, REFS_DIRNAME})
    if config.out in reserved:
        raise ValueError(
            f"export.out={config.out!r} collides with a source-of-truth "
            f"directory (document slug, `{RESEARCH_DIRNAME}/`, or "
            f"`{REFS_DIRNAME}/`). The export rebuilds its out dir by "
            f"deleting it; refusing. Suggested fix: choose a dedicated "
            f"name like `SHARE`."
        )


def _resolve_cover(
    project_dir: Path,
    config: ExportConfig,
    reserved_top_level_names: Sequence[str] = (),
) -> Optional[FilePlan]:
    """Resolve ``export.cover`` (issue #757) into a top-level :class:`FilePlan`.

    Returns ``None`` when ``export.cover`` is unset. Raises ``ValueError``
    when ``export.cover_as`` collides with :data:`MARKER_FILENAME` (the
    AC's explicit collision requirement) or any other reserved top-level
    export-root name (``research/``, a planned ``NN-<slug>/`` doc dir —
    defense-in-depth, same posture as :func:`_check_out_collisions`), or
    when ``export.cover`` does not resolve to an existing file under
    ``project_dir``. All checks here are pure config checks (no
    filesystem I/O) and run before the filesystem check.
    """
    if config.cover is None:
        return None
    reserved = {MARKER_FILENAME, *reserved_top_level_names}
    if config.cover_as in reserved:
        raise ValueError(
            f"export.cover_as={config.cover_as!r} collides with a "
            f"reserved top-level export-root name (the `{MARKER_FILENAME}` "
            f"rebuild marker, `{RESEARCH_DIRNAME}/`, or a planned document "
            f"directory) — refusing. Suggested fix: choose a different "
            f"`export.cover_as` name."
        )
    source = (project_dir / config.cover).resolve()
    if not source.is_file():
        raise ValueError(
            f"export.cover={config.cover!r} does not resolve to a file at "
            f"{source}. Suggested fix: check the path is relative to the "
            f"project root and that the file exists."
        )
    return FilePlan(source=source, target_rel=Path(config.cover_as))


def build_plan(
    project_dir: Path,
    brief: "ProjectBrief",
    config: ExportConfig,
) -> SharePlan:
    """Build the full export plan. Pure — never writes to disk.

    Raises
    ------
    ValueError
        On ``export.order`` unknown slugs, an ``export.out`` name
        colliding with a source-of-truth directory, an ``export.cover_as``
        colliding with a reserved top-level export-root name (the
        ``EXPORT.md`` marker, ``research/``, or a planned document
        directory), or an ``export.cover`` path that does not resolve to
        an existing file.
    """
    project_dir = Path(project_dir).resolve()
    _check_out_collisions(project_dir, brief, config)
    ordered, excluded, ordering_source = _resolve_ordering(brief, config)
    reserved_top_level_names = [RESEARCH_DIRNAME] + [
        f"{ordinal:02d}-{slug}" for ordinal, slug in enumerate(ordered)
    ]
    cover_file = _resolve_cover(project_dir, config, reserved_top_level_names)

    plan = SharePlan(
        project_dir=project_dir,
        project_name=brief.project,
        config=config,
        out_dir=project_dir / config.out,
        ordering_source=ordering_source,
    )
    plan.cover_file = cover_file
    plan.excluded_slugs = excluded
    for slug in excluded:
        plan.notes.append(
            f"`{slug}` is listed in BRIEF.documents but omitted from "
            f"export.order — excluded from this export."
        )

    for ordinal, slug in enumerate(ordered):
        collection = collect_doc(project_dir, slug)
        target_dirname = f"{ordinal:02d}-{slug}"
        doc = DocPlan(
            slug=slug,
            ordinal=ordinal,
            target_dirname=target_dirname,
            collection=collection,
        )
        if collection.failed:
            plan.docs.append(doc)
            continue

        assert collection.resolved_dir is not None
        doc.files = _manifest_for_tree(
            collection.resolved_dir,
            Path(target_dirname),
            config.strip,
            top_level_only=not config.include_assets,
        )
        if not config.include_assets:
            doc.notes.append(
                "include_assets=false: subdirectories of the version dir "
                "were skipped (top-level files only)."
            )
        if not collection.pdfs:
            doc.notes.append("no rendered PDF in the resolved version dir.")

        if config.include_refs and collection.refs_dir is not None:
            doc.files.extend(
                _manifest_for_tree(
                    collection.refs_dir,
                    Path(target_dirname) / REFS_DIRNAME,
                    config.strip,
                )
            )
        plan.docs.append(doc)

    if config.include_research:
        research_dir = collect_research(project_dir)
        if research_dir is not None:
            plan.research_files = _manifest_for_tree(
                research_dir,
                Path(RESEARCH_DIRNAME),
                config.strip,
            )

    return plan


__all__ = [
    "DocPlan",
    "FilePlan",
    "MARKER_FILENAME",
    "ORDERING_DOCUMENTS",
    "ORDERING_EXPORT_ORDER",
    "OUT_ABSENT",
    "OUT_EMPTY",
    "OUT_FOREIGN",
    "OUT_MARKER",
    "STRUCTURAL_EXCLUDES",
    "SharePlan",
    "build_plan",
    "inspect_out_dir",
    "is_stripped",
]
