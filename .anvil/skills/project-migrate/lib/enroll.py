"""Single-file enrollment planning for `anvil:project-migrate` (issue #406).

Wraps a loose document (a flat ``.md`` / ``.tex`` file in a topical
directory) into a project/thread: ``<project>/<slug>/<slug>.1/<slug>.<ext>``
plus a ``documents:`` entry in the project BRIEF.

Design notes
------------

- **Pure planner — no mutations.** Like :mod:`detect` and :mod:`plan`,
  this module reads files but never writes. The dry-run contract depends
  on it.
- **Reuses the migrate plan types.** An enrollment is expressible as a
  :class:`plan.DocumentPlan` (one :class:`plan.Rename` + one
  :class:`plan.BriefMergeOp`), so the per-doc snapshot/rollback
  atomicity and the ``git mv`` preference in :mod:`apply` come for free.
  The plan is tagged :data:`detect.Shape.ENROLL` (a plan-mode tag, not a
  detected shape) and carries ``brief_mode`` so the apply step knows
  whether to surgically append to an existing BRIEF or synthesize a
  fresh one.
- **Two-phase batch semantics.** Plan-time validation (this module)
  aborts the whole batch BEFORE any mutation: slug collisions (existing
  and intra-batch), non-``.md``/``.tex`` inputs, already-enrolled
  inputs, malformed existing BRIEFs. Apply-time failures isolate per
  document via the existing snapshot machinery, and the BRIEF is
  written for the succeeded subset (see ``apply._write_enroll_brief``).
- **Guarded ``anvil.lib`` imports.** The richer validation tier
  (strict BRIEF parse, two-tier artifact-type registry, thread-root
  discovery) is consumed through function-local imports with
  ``ImportError`` fallbacks, preserving the skill's no-fragile-import-
  chain property at install time.

Public API
----------

- ``EnrollError`` — typed plan-time refusal (a ``ValueError``).
- ``derive_slug(stem)`` — slug + captured ISO date from a filename stem.
- ``validate_explicit_slug(slug)`` — canonical-form check for ``--slug``.
- ``resolve_project(file, explicit_project=None)`` — project-root
  resolution (explicit > walk-up > propose file's parent).
- ``build_enroll_plan(files, ...)`` — top-level entry; returns a
  :class:`plan.Plan`.
"""

from __future__ import annotations

import re
import warnings
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from .apply import _detect_git_repo
from .detect import (
    BRIEF_FILENAME,
    COUNSEL_MEMO_FILENAME,
    PROVISIONAL_BODY_FILENAME,
    Shape,
    _VERSION_DIR_RE,
    _extract_frontmatter,
    _has_project_brief,
    _project_brief_slugs,
)
from .plan import (
    BriefMergeOp,
    DocumentPlan,
    Plan,
    Rename,
    _infer_tex_artifact_type,
    _read_text_lenient,
)


class EnrollError(ValueError):
    """Plan-time enrollment refusal.

    Raised BEFORE any mutation — the whole batch aborts on the first
    plan-time error (issue #406 two-phase batch semantics).
    """


# Canonical slug form. Mirrors the project-share bare-output-name
# precedent (`anvil/skills/project-share/lib/config.py`): lowercase
# alphanumerics + hyphens, no path separators, no leading hyphen.
_CANONICAL_SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")

# ISO date tokens at the head or tail of a filename stem. The issue's
# own examples show both forms: `2026-05-19-<topic>.md` (prefix) and
# `<topic>-2026-05-19.md` (suffix).
_DATE_PREFIX_RE = re.compile(r"^(?P<date>\d{4}-\d{2}-\d{2})[-_ ]+")
_DATE_SUFFIX_RE = re.compile(r"[-_ .]+(?P<date>\d{4}-\d{2}-\d{2})$")

# Enrollable inputs. Anything else is a plan-time hard error.
_ENROLLABLE_SUFFIXES = (".md", ".tex")

# Filenames that are project/infrastructure markers, never bodies.
_REFUSED_FILENAMES = frozenset({BRIEF_FILENAME, "README.md"})

# The memo-class no-information default (mirrors plan.BriefMergeOp).
_DEFAULT_ARTIFACT_TYPE = "investment-memo"


# ---------------------------------------------------------------------------
# Slug derivation
# ---------------------------------------------------------------------------


def derive_slug(stem: str) -> Tuple[str, Optional[str]]:
    """Derive ``(slug, captured_date)`` from a filename stem.

    Rules (issue #406, curator-resolved):

    - Strip a leading ISO date token (``2026-05-19-<topic>``) and/or a
      trailing one (``<topic>-2026-05-19``), capturing the date (the
      leading one wins when both are present).
    - Lowercase; collapse ``[^a-z0-9]+`` runs to ``-``; trim leading /
      trailing ``-``.
    - An empty result is a hard error demanding ``--slug``.
    """
    date: Optional[str] = None
    working = stem.strip()

    m = _DATE_PREFIX_RE.match(working)
    if m is not None:
        date = m.group("date")
        working = working[m.end():]

    m = _DATE_SUFFIX_RE.search(working)
    if m is not None:
        if date is None:
            date = m.group("date")
        working = working[: m.start()]

    slug = re.sub(r"[^a-z0-9]+", "-", working.lower()).strip("-")
    if not slug:
        raise EnrollError(
            f"Could not derive a slug from filename stem {stem!r} "
            f"(nothing left after date-stripping and sanitization). "
            f"Suggested fix: pass --slug <slug> explicitly."
        )
    return slug, date


def validate_explicit_slug(slug: str) -> str:
    """Validate an operator-provided ``--slug`` value.

    The operator value must ALREADY be canonical
    (``^[a-z0-9][a-z0-9-]*$``, no path separators) — it is rejected
    rather than silently re-sanitized (the project-share bare-name
    precedent).
    """
    if "/" in slug or "\\" in slug or not _CANONICAL_SLUG_RE.match(slug):
        raise EnrollError(
            f"--slug {slug!r} is not canonical. A slug must match "
            f"^[a-z0-9][a-z0-9-]*$ (lowercase alphanumerics and "
            f"hyphens, no path separators). Suggested fix: pass an "
            f"already-canonical slug — the value is not re-sanitized."
        )
    return slug


# ---------------------------------------------------------------------------
# Project resolution + refusal predicates
# ---------------------------------------------------------------------------


def resolve_project(
    file: Path, explicit_project: Optional[Path] = None
) -> Tuple[Path, bool]:
    """Resolve the enclosing project root for ``file``.

    Returns ``(project_dir, brief_file_exists)``.

    Resolution order (issue #406):

    1. ``--project`` given → use it (must exist; BRIEF optional —
       created if absent).
    2. Walk up from the file's parent looking for a directory whose
       ``BRIEF.md`` is a project BRIEF (non-empty ``documents:`` list),
       bounded by the git repo root (when in a repo) or the filesystem
       root.
    3. Propose the file's parent as a NEW project root (BRIEF will be
       synthesized).
    """
    if explicit_project is not None:
        project = Path(explicit_project).resolve()
        if not project.is_dir():
            raise EnrollError(
                f"--project {explicit_project} does not exist or is "
                f"not a directory."
            )
        return project, (project / BRIEF_FILENAME).is_file()

    start = Path(file).resolve().parent
    git_info = _detect_git_repo(start)
    boundary = git_info.repo_root

    current = start
    while True:
        if _has_project_brief(current):
            return current, True
        if boundary is not None and current == boundary:
            break
        parent = current.parent
        if parent == current:
            break
        current = parent

    return start, (start / BRIEF_FILENAME).is_file()


def _refuse_already_enrolled(file: Path) -> None:
    """Raise :class:`EnrollError` when ``file`` is already inside a thread.

    Two predicates (issue #406 — this is also the idempotency story:
    re-enrolling is a refusal, not a duplicate):

    1. Any ancestor directory matching the ``<stem>.<N>`` version-dir
       pattern.
    2. ``discover_thread_root(file)`` resolving (guarded import — the
       check is skipped when ``anvil.lib`` is unavailable; predicate 1
       still covers the version-dir case).
    """
    resolved = Path(file).resolve()
    for ancestor in resolved.parents:
        if _VERSION_DIR_RE.match(ancestor.name) is not None:
            raise EnrollError(
                f"{file} is already inside a version directory "
                f"(`{ancestor.name}/`) — it is already enrolled. "
                f"Re-enrolling is a refusal, not a duplicate."
            )
    try:
        from anvil.lib.project_discovery import discover_thread_root
    except ImportError:
        return
    result = discover_thread_root(resolved)
    if result is not None:
        raise EnrollError(
            f"{file} already resolves to thread `{result.slug}` at "
            f"{result.thread_root} — it is already enrolled. "
            f"Re-enrolling is a refusal, not a duplicate."
        )


def _validate_input_file(file: Path) -> None:
    """Plan-time per-file refusals: existence, extension, filename."""
    if not file.is_file():
        raise EnrollError(
            f"Cannot enroll {file}: not an existing file."
        )
    if file.name in _REFUSED_FILENAMES:
        raise EnrollError(
            f"Cannot enroll {file}: `{file.name}` is a project / "
            f"infrastructure marker, not a document body."
        )
    if file.name == COUNSEL_MEMO_FILENAME:
        raise EnrollError(
            f"Cannot enroll {file}: `{COUNSEL_MEMO_FILENAME}` is a "
            f"finalize-output counsel memo (a companion to a provisional "
            f"body, written into `<thread>.counsel/`), not a fileable "
            f"document body. Suggested fix: enroll the "
            f"`{PROVISIONAL_BODY_FILENAME}` body this counsel memo "
            f"accompanies instead."
        )
    if file.suffix not in _ENROLLABLE_SUFFIXES:
        raise EnrollError(
            f"Cannot enroll {file}: only "
            f"{' / '.join(_ENROLLABLE_SUFFIXES)} files are enrollable; "
            f"got `{file.suffix or '(no extension)'}`."
        )
    _refuse_already_enrolled(file)


def _check_existing_brief(project_dir: Path) -> List[str]:
    """Validate an existing BRIEF and return its declared slugs.

    Two tiers:

    1. Skill-local minimal check: the file must carry parseable
       frontmatter with a non-empty ``documents:`` list. A ``BRIEF.md``
       that fails this (e.g. a pre-#283 thread-level brief, or
       malformed YAML) is a hard error — never modify a BRIEF we can't
       parse.
    2. ``anvil.lib`` strict parse with ``validate_dirs=True`` (guarded
       import). A "configuration drift" failure (thread-shaped dirs not
       listed in the BRIEF) gets a targeted suggestion: run plain
       ``project-migrate`` on the project first.
    """
    brief_path = project_dir / BRIEF_FILENAME
    try:
        text = brief_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise EnrollError(
            f"Cannot read existing BRIEF at {brief_path}: {exc}"
        ) from exc
    fm = _extract_frontmatter(text)
    docs = fm.get("documents") if isinstance(fm, dict) else None
    if not isinstance(docs, list) or not docs:
        raise EnrollError(
            f"Existing BRIEF at {brief_path} is not a parseable project "
            f"BRIEF (no frontmatter `documents:` list). Refusing to "
            f"modify a BRIEF that cannot be parsed. Suggested fix: "
            f"repair the BRIEF, or pass --project pointing at a "
            f"different project root."
        )

    try:
        from anvil.lib.project_brief import load_project_brief_strict
    except ImportError:
        return _project_brief_slugs(project_dir)

    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            load_project_brief_strict(project_dir, validate_dirs=True)
    except (ValueError, FileNotFoundError) as exc:
        message = str(exc)
        if "Configuration drift" in message:
            raise EnrollError(
                f"Project {project_dir} contains thread-shaped "
                f"directories not listed in its BRIEF — enrollment "
                f"would fail post-write validation. Suggested fix: run "
                f"/anvil:project-migrate {project_dir} first to bring "
                f"the project to the canonical shape, then enroll. "
                f"Underlying error: {message}"
            ) from exc
        raise EnrollError(
            f"Existing BRIEF at {brief_path} fails strict parsing — "
            f"refusing to modify a BRIEF that cannot be parsed. "
            f"Underlying error: {message}"
        ) from exc

    return _project_brief_slugs(project_dir)


def _thread_shaped_dirs(project_dir: Path) -> List[str]:
    """Return on-disk thread-root-shaped subdirectory names.

    A subdirectory qualifies when its name appears as the stem of at
    least one ``<name>.<N>`` child. Local mirror of
    ``project_brief._on_disk_slug_dirs`` (kept skill-local so the
    collision check works without the ``anvil.lib`` import tier).
    """
    out: List[str] = []
    try:
        children = list(project_dir.iterdir())
    except OSError:
        return out
    for child in children:
        if not child.is_dir() or child.name.startswith("."):
            continue
        try:
            grandchildren = list(child.iterdir())
        except OSError:
            continue
        for gc in grandchildren:
            if not gc.is_dir():
                continue
            m = _VERSION_DIR_RE.match(gc.name)
            if m is not None and m.group("stem") == child.name:
                out.append(child.name)
                break
    return out


def _validate_artifact_type_choice(
    value: str, project_dir: Path
) -> str:
    """Validate ``--artifact-type`` through the #394 two-tier path.

    Tier 1: :data:`anvil.lib.project_brief.REGISTERED_ARTIFACT_TYPES`.
    Tier 2: consumer-declared types discovered via
    ``discover_consumer_artifact_types``. Anything else is a hard
    error listing both sets. Guarded import: when ``anvil.lib`` is
    unavailable the value passes through (the post-write strict parse
    is the backstop).
    """
    try:
        from anvil.lib.project_brief import (
            REGISTERED_ARTIFACT_TYPES,
            discover_consumer_artifact_types,
        )
    except ImportError:
        return value
    consumer_types = discover_consumer_artifact_types(project_dir)
    if value in REGISTERED_ARTIFACT_TYPES or value in consumer_types:
        return value
    raise EnrollError(
        f"--artifact-type {value!r} is not a registered or "
        f"consumer-declared artifact type. Registered: "
        f"{list(REGISTERED_ARTIFACT_TYPES)}. Consumer-declared: "
        f"{sorted(consumer_types)}."
    )


# ---------------------------------------------------------------------------
# Plan construction
# ---------------------------------------------------------------------------


def _infer_artifact_type_for_file(
    file: Path,
) -> Tuple[str, str]:
    """Infer ``(artifact_type, todo_comment)`` for an enrolled file.

    Inference is ALWAYS paired with a TODO marker (never the migrate
    path's silent default):

    - filename ``provisional.tex`` → ``ip-uspto-provisional`` (issue
      #503 — FILENAME-driven, never ``\\documentclass`` content: anvil's
      provisional and full ip-uspto specs share
      ``\\documentclass{anvil-uspto}``, so content cannot disambiguate
      them; SKILL.md:160 forbids that inference).
    - ``.md`` → ``investment-memo`` (memo-class default).
    - ``.tex`` with ``\\documentclass{anvil-proposal}`` → ``proposal``;
      any other ``\\documentclass`` → ``paper``; no ``\\documentclass``
      → memo-class default.
    """
    if file.name == PROVISIONAL_BODY_FILENAME:
        return "ip-uspto-provisional", (
            f"TODO(operator): confirm — recognized from "
            f"{PROVISIONAL_BODY_FILENAME} body filename"
        )
    if file.suffix == ".tex":
        inferred = _infer_tex_artifact_type(_read_text_lenient(file))
        if inferred is not None:
            return inferred, (
                f"TODO(operator): confirm — inferred from {file.name} "
                f"\\documentclass"
            )
        return _DEFAULT_ARTIFACT_TYPE, (
            f"TODO(operator): confirm — could not infer from "
            f"{file.name}; defaulted"
        )
    return _DEFAULT_ARTIFACT_TYPE, (
        "TODO(operator): confirm — memo-class default for an enrolled "
        "markdown file"
    )


def build_enroll_plan(
    files: Sequence[Path],
    *,
    project: Optional[Path] = None,
    slug: Optional[str] = None,
    artifact_type: Optional[str] = None,
) -> Plan:
    """Build an enrollment :class:`plan.Plan` for ``files``.

    Every check here is plan-time (pre-mutation); any failure raises
    :class:`EnrollError` and aborts the WHOLE batch before anything is
    moved.

    Parameters
    ----------
    files
        Loose ``.md`` / ``.tex`` files to enroll. A batch enrolls into
        ONE project — files resolving to different projects abort.
    project
        Optional explicit project root (``--project``).
    slug
        Optional explicit slug (``--slug``) — single-file batches only;
        must already be canonical.
    artifact_type
        Optional explicit artifact type (``--artifact-type``) —
        validated through the #394 two-tier registry; applies to every
        file in the batch.
    """
    file_paths = [Path(f) for f in files]
    if not file_paths:
        raise EnrollError("No files given to enroll.")
    if slug is not None and len(file_paths) > 1:
        raise EnrollError(
            f"--slug applies to a single file; got {len(file_paths)} "
            f"files. Suggested fix: enroll the files separately, or "
            f"drop --slug to derive slugs from filenames."
        )
    if slug is not None:
        validate_explicit_slug(slug)

    # Per-file refusals.
    for f in file_paths:
        _validate_input_file(f)

    # Project resolution — the batch must agree on ONE project.
    resolutions = [resolve_project(f, project) for f in file_paths]
    project_dirs = {p for p, _ in resolutions}
    if len(project_dirs) > 1:
        listed = ", ".join(str(p) for p in sorted(project_dirs))
        raise EnrollError(
            f"Batch enrollment spans multiple project roots: {listed}. "
            f"Suggested fix: pass --project <dir> to pin one project, "
            f"or enroll the files in separate invocations."
        )
    project_dir = next(iter(project_dirs))
    brief_exists = resolutions[0][1]

    # Existing-BRIEF validation (never modify a BRIEF we can't parse).
    existing_slugs: List[str] = []
    if brief_exists:
        existing_slugs = _check_existing_brief(project_dir)
    else:
        # Creating a fresh BRIEF: pre-existing thread-shaped dirs would
        # be unlisted in the synthesized BRIEF and fail validation.
        stray = sorted(_thread_shaped_dirs(project_dir))
        if stray:
            raise EnrollError(
                f"Project root {project_dir} has no BRIEF but contains "
                f"thread-shaped directories: {stray}. Suggested fix: "
                f"run /anvil:project-migrate {project_dir} first to "
                f"generate a BRIEF covering them, then enroll."
            )

    if artifact_type is not None:
        artifact_type = _validate_artifact_type_choice(
            artifact_type, project_dir
        )

    on_disk_dirs = set(_thread_shaped_dirs(project_dir))

    # Derive slugs + collision checks (existing + intra-batch).
    seen: Dict[str, Path] = {}
    enroll_plan = Plan(project_dir=project_dir, shape=Shape.ENROLL)
    enroll_plan.brief_mode = "append" if brief_exists else "render"
    enroll_plan.synthesize_brief = not brief_exists
    enroll_plan.preexisting_brief_slugs = list(existing_slugs)

    for f in file_paths:
        resolved = f.resolve()
        if slug is not None:
            doc_slug = slug
            _, date = derive_slug(resolved.stem)
        else:
            doc_slug, date = derive_slug(resolved.stem)

        if doc_slug in existing_slugs:
            raise EnrollError(
                f"Slug collision: `{doc_slug}` (from {f.name}) is "
                f"already listed in {project_dir / BRIEF_FILENAME}. "
                f"Suggested fix: pass --slug with a different name."
            )
        if doc_slug in on_disk_dirs or (project_dir / doc_slug).exists():
            raise EnrollError(
                f"Slug collision: `{doc_slug}` (from {f.name}) "
                f"conflicts with existing path "
                f"{project_dir / doc_slug}. Suggested fix: pass --slug "
                f"with a different name."
            )
        if doc_slug in seen:
            raise EnrollError(
                f"Slug collision within the batch: both "
                f"{seen[doc_slug].name} and {f.name} derive slug "
                f"`{doc_slug}`. Suggested fix: enroll one of them "
                f"separately with --slug."
            )
        seen[doc_slug] = f

        if artifact_type is not None:
            doc_artifact_type = artifact_type
            inferred = False
            todo: Optional[str] = None
        else:
            doc_artifact_type, todo = _infer_artifact_type_for_file(
                resolved
            )
            inferred = True

        slug_comment = f"enrolled-from: {resolved.name}"
        if date is not None:
            slug_comment += f" (date: {date})"

        target_dir = project_dir / doc_slug
        target_body = (
            target_dir / f"{doc_slug}.1" / f"{doc_slug}{resolved.suffix}"
        )

        doc = DocumentPlan(
            slug=doc_slug,
            source_dir=resolved.parent,
            target_dir=target_dir,
            renames=[Rename(source=resolved, target=target_body)],
            brief_merge=BriefMergeOp(
                slug=doc_slug,
                artifact_type=doc_artifact_type,
                inferred=inferred,
                todo_comment=todo,
                slug_comment=slug_comment,
            ),
        )
        doc.notes.append(
            f"Enroll: {resolved.name} → "
            f"{doc_slug}/{doc_slug}.1/{doc_slug}{resolved.suffix}"
        )
        log_line = (
            f"enrolled `{resolved.name}` as "
            f"`{doc_slug}/{doc_slug}.1/{doc_slug}{resolved.suffix}` "
            f"(version 1)"
        )
        if date is not None:
            log_line += f" — source date: {date}"
            doc.notes.append(
                f"{doc_slug}: date `{date}` stripped from the filename; "
                f"preserved as a YAML comment on the BRIEF entry and in "
                f"the body enrollment log."
            )
        doc.enrollment_log.append(log_line)

        if inferred:
            doc.notes.append(
                f"{doc_slug}: artifact_type inferred as "
                f"'{doc_artifact_type}' — confirm in BRIEF (TODO marker "
                f"emitted)."
            )
            doc.operator_todos.append(
                f"`{doc_slug}`: confirm `artifact_type: "
                f"{doc_artifact_type}` (inferred at enrollment from "
                f"{resolved.name})."
            )
        if resolved.suffix == ".tex":
            doc.notes.append(
                f"{doc_slug}: LaTeX body renamed "
                f"{resolved.name} → {doc_slug}.tex (new enrollments "
                f"have no external-tooling carve-out — the enclosing "
                f"move already breaks any path-based consumer). "
                f"References to the old path elsewhere are NOT "
                f"rewritten (out of scope)."
            )

        enroll_plan.documents.append(doc)

    return enroll_plan


__all__ = [
    "EnrollError",
    "build_enroll_plan",
    "derive_slug",
    "resolve_project",
    "validate_explicit_slug",
]
