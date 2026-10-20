"""vN report-dir adoption planning for `anvil:project-migrate` (issue #432).

Adopts a foreign ``v{N}/`` version-dir family (the sphere-survey report
grammar: ``projects/<proj>/reports/v3/`` + ``v3.review/`` siblings) into
the canonical anvil shape: ``<project>/<slug>/<slug>.{N}/`` with
``<slug>.{N}.<tag>`` critic siblings.

Design notes
------------

- **Pure planner — no mutations.** Mirrors :mod:`enroll` exactly: this
  module reads the tree but never writes. The dry-run contract depends
  on it.
- **Reuses the migrate plan types.** A vN adoption is expressible as ONE
  :class:`plan.DocumentPlan` (one :class:`plan.Rename` per version dir /
  sidecar + one :class:`plan.BriefMergeOp`), so the per-doc
  snapshot/rollback atomicity and the ``git mv`` preference in
  :mod:`apply` come for free. The plan is tagged
  :data:`detect.Shape.ADOPT_VN` (a plan-mode tag, not a detected shape —
  the ENROLL precedent; ``detect_shape`` never returns it and
  ``_classify`` is untouched) and carries ``brief_mode`` so the apply
  step dispatches the BRIEF write through the enroll-style path: a
  **surgical textual append** when an enclosing project BRIEF exists
  (#406/#416 — never re-render an operator BRIEF) or a **synthesized
  starter BRIEF** with ``# TODO(operator)`` markers otherwise (#408).
- **Strictly mechanical, operator-confirmable.** Every refusal is
  plan-time, BEFORE any mutation:

  - minor-versioned oddballs (``v14.1``) refuse the whole family,
    naming each offending dir with a suggested manual target (the next
    free integer) — a ``--renumber`` escape hatch is deferred until
    canary friction demands it;
  - ambiguous leading-zero numbering (``v07/`` + ``v7/`` parsing to
    the same version slot, or duplicate sidecar slots like
    ``v07.review/`` + ``v7.review/``) refuses the whole family at scan
    time, naming every colliding dir per slot (#458) — a LONE ``v07``
    still adopts, normalized to ``<slug>.7``;
  - target collisions (``<slug>.{N}`` already on disk, slug already in
    the BRIEF, slug dir occupied) refuse with a ``--slug`` suggestion;
  - a malformed existing BRIEF refuses (never modify a BRIEF we can't
    parse);
  - a BRIEF-less project root with other thread-shaped dirs refuses
    (run plain ``project-migrate`` first — the enroll precedent).

  Stray non-versioned dirs (and orphan ``v{N}.<tag>`` sidecars whose
  ``v{N}`` is absent) are left untouched and reported.
- **Bodies are never renamed.** Observed body files inside the version
  dirs are recorded with a deferral note — the #408 carve-out applies
  verbatim (the dir-level rename moves them along; their names are
  external-tooling surface).
- **Idempotence.** Re-running on an adopted tree finds no ``v{N}``
  family and yields an empty (no-op) plan.

Public API
----------

- ``AdoptVnError`` — typed plan-time refusal (a ``ValueError``).
- ``build_adopt_vn_plan(directory, ...)`` — top-level entry; returns a
  :class:`plan.Plan`.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .apply import _detect_git_repo
from .detect import BRIEF_FILENAME, Shape, _has_project_brief
from .enroll import (
    EnrollError,
    _check_existing_brief,
    _thread_shaped_dirs,
    _validate_artifact_type_choice,
    validate_explicit_slug,
)
from .plan import BriefMergeOp, DocumentPlan, Plan, Rename


class AdoptVnError(ValueError):
    """Plan-time adoption refusal.

    Raised BEFORE any mutation — the whole family aborts on the first
    plan-time error (one family per ``--adopt-vn`` invocation; the
    batch-enroll abort-pre-mutation contract).
    """


# The foreign vN version-dir grammar: `v` + integer, nothing else.
_VN_DIR_RE = re.compile(r"^v(?P<num>\d+)$")

# Minor-versioned oddballs (`v14.1`, `v2.0.1`): plan-time refusal —
# there is no mechanical integer target for them.
_VN_MINOR_RE = re.compile(r"^v(?P<major>\d+)(?:\.\d+)+$")

# A `v{N}.<tag>` critic sidecar (observed in the wild: `v{N}.review/`).
# The tag must be a single dot-free word starting with a non-digit so
# `v14.1` cannot false-match as a sidecar with tag "1".
_VN_SIDECAR_RE = re.compile(r"^v(?P<num>\d+)\.(?P<tag>[A-Za-z_][^.]*)$")

# A versioned critic tag (`review-v2`) — renaming it would re-create a
# FOREIGN name under the new stem (`<slug>.3.review-v2` fires
# project-scout's foreign guard, predicate iii). Tag vocabulary mapping
# is Phase 2 (`--tag-map`, issue #432 curation) — Phase 1 refuses.
_FOREIGN_TAG_SUFFIX_RE = re.compile(r"-v\d+$")

# The adopt-vn inferred default (issue #432): the mode targets report
# dirs, and nothing is guessed silently — the inference is ALWAYS
# paired with a TODO(operator) marker. `report` is a registered
# skill-identity artifact type (the #408 `pub`/`paper` registry precedent).
_DEFAULT_ADOPT_ARTIFACT_TYPE = "report"

# Body-ish files recorded (never renamed — the #408 carve-out).
_OBSERVED_BODY_SUFFIXES = (".md", ".tex")


def _sanitize_default_slug(name: str) -> str:
    """Derive the default slug from the enclosing dir name.

    Same sanitization as :func:`enroll.derive_slug`'s tail step
    (lowercase; collapse non-alphanumeric runs to ``-``; trim). An
    empty result is a hard error demanding ``--slug``.
    """
    slug = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")
    if not slug:
        raise AdoptVnError(
            f"Could not derive a slug from directory name {name!r} "
            f"(nothing left after sanitization). Suggested fix: pass "
            f"--slug <slug> explicitly."
        )
    return slug


def _resolve_enclosing_project(directory: Path) -> Tuple[Path, bool]:
    """Resolve the enclosing project root for the vN family dir.

    Returns ``(project_dir, brief_file_exists)``. Mirrors
    :func:`enroll.resolve_project`: walk up from the family dir's
    PARENT looking for a directory whose ``BRIEF.md`` is a project
    BRIEF, bounded by the git repo root (when in a repo) or the
    filesystem root; otherwise propose the parent as a NEW project
    root (BRIEF will be synthesized).
    """
    start = Path(directory).resolve().parent
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


def _format_ambiguous_slot(names: List[str], slot_desc: str) -> str:
    """One refusal clause for a parsed slot claimed by >1 directory name.

    Leading-zero twins (``v07/`` + ``v7/``, issue #458) parse to the
    same integer slot; a dict-keyed scan would silently drop all but
    one, and same-slot sidecars would plan renames to one shared
    target. Shared with :mod:`adopt_family` (the
    ``_FOREIGN_TAG_SUFFIX_RE`` import precedent).
    """
    quoted = [f"`{n}/`" for n in sorted(names)]
    if len(quoted) == 2:
        joined = f"{quoted[0]} and {quoted[1]}"
    else:
        joined = ", ".join(quoted[:-1]) + " and " + quoted[-1]
    verb = "both" if len(quoted) == 2 else "all"
    return f"{joined} {verb} parse to {slot_desc}"


def _scan_family(
    directory: Path,
) -> Tuple[Dict[int, Path], Dict[int, List[Tuple[str, Path]]], List[str], List[str]]:
    """Scan ``directory`` for the vN family.

    Returns ``(versions, sidecars, minors, strays)`` where ``versions``
    maps N → version dir, ``sidecars`` maps N → ``[(tag, dir), ...]``,
    ``minors`` lists minor-versioned oddball dir names, and ``strays``
    lists non-versioned dir names left untouched (including orphan
    sidecars whose ``v{N}`` is absent — folded in by the caller).

    A version slot or sidecar ``(N, tag)`` slot claimed by more than
    one directory name (the leading-zero collapse, issue #458:
    ``v07/`` + ``v7/``, ``v07.review/`` + ``v7.review/``) is a
    scan-time refusal naming every colliding dir per slot — BEFORE any
    slug/BRIEF/collision work.
    """
    version_claims: Dict[int, List[Path]] = {}
    sidecar_claims: Dict[Tuple[int, str], List[Path]] = {}
    minors: List[str] = []
    strays: List[str] = []

    try:
        children = sorted(directory.iterdir())
    except OSError as exc:
        raise AdoptVnError(
            f"Cannot read directory {directory}: {exc}"
        ) from exc

    for child in children:
        if not child.is_dir():
            continue  # Loose files stay where they are; not family grammar.
        name = child.name
        m = _VN_DIR_RE.match(name)
        if m is not None:
            version_claims.setdefault(int(m.group("num")), []).append(child)
            continue
        if _VN_MINOR_RE.match(name) is not None:
            minors.append(name)
            continue
        m = _VN_SIDECAR_RE.match(name)
        if m is not None:
            sidecar_claims.setdefault(
                (int(m.group("num")), m.group("tag")), []
            ).append(child)
            continue
        strays.append(name)

    ambiguous: List[str] = []
    versions: Dict[int, Path] = {}
    for num in sorted(version_claims):
        claimants = version_claims[num]
        if len(claimants) > 1:
            ambiguous.append(
                _format_ambiguous_slot(
                    [c.name for c in claimants], f"version {num}"
                )
            )
        else:
            versions[num] = claimants[0]

    sidecars: Dict[int, List[Tuple[str, Path]]] = {}
    for num, tag in sorted(sidecar_claims):
        claimants = sidecar_claims[(num, tag)]
        if num not in version_claims:
            # Orphan sidecar(s) (no matching v{N}) — untouched, reported.
            strays.extend(c.name for c in claimants)
            continue
        if len(claimants) > 1:
            ambiguous.append(
                _format_ambiguous_slot(
                    [c.name for c in claimants],
                    f"the version-{num} `{tag}` sidecar",
                )
            )
            continue
        sidecars.setdefault(num, []).append((tag, claimants[0]))

    if ambiguous:
        raise AdoptVnError(
            "Ambiguous version numbering: "
            + "; ".join(ambiguous)
            + " — rename one of each colliding set manually, then "
            "re-run --adopt-vn. Nothing was modified."
        )

    return versions, sidecars, sorted(minors), sorted(strays)


def _refuse_minors(minors: List[str], versions: Dict[int, Path]) -> None:
    """Refuse the whole family when minor-versioned oddballs exist.

    Pre-mutation, naming each offending dir with a suggested manual
    target: the next free integer after every observed (and
    already-suggested) version number.
    """
    taken = set(versions.keys())
    next_free = (max(taken) + 1) if taken else 1
    suggestions: List[str] = []
    for name in minors:
        while next_free in taken:
            next_free += 1
        suggestions.append(f"`{name}/` → rename manually to `v{next_free}/`")
        taken.add(next_free)
        next_free += 1
    raise AdoptVnError(
        "Minor-versioned dirs found — vN adoption is strictly "
        "mechanical and cannot renumber them: "
        + "; ".join(suggestions)
        + ". Rename the offending dirs to free integer versions "
        "(suggested above), then re-run --adopt-vn. Nothing was "
        "modified."
    )


def _observed_body_filenames(version_dirs: List[Path]) -> List[str]:
    """Collect body-ish filenames observed across the version dirs."""
    seen: set = set()
    for vd in version_dirs:
        try:
            for entry in vd.iterdir():
                if entry.is_file() and entry.suffix in _OBSERVED_BODY_SUFFIXES:
                    seen.add(entry.name)
        except OSError:
            continue
    return sorted(seen)


def build_adopt_vn_plan(
    directory: Path,
    *,
    slug: Optional[str] = None,
    artifact_type: Optional[str] = None,
) -> Plan:
    """Build a vN-adoption :class:`plan.Plan` for ``directory``.

    Every check here is plan-time (pre-mutation); any failure raises
    :class:`AdoptVnError` and aborts the WHOLE family before anything
    is moved. A directory with no ``v{N}`` family yields an EMPTY plan
    (``plan.is_noop``) — re-running on an adopted tree is a no-op, not
    an error.

    Parameters
    ----------
    directory
        The directory holding the ``v{N}/`` family (e.g.
        ``projects/<proj>/reports/``).
    slug
        Optional explicit slug (``--slug``) — must already be canonical
        (rejected, never re-sanitized; the #406 precedent). Defaults to
        the sanitized enclosing-dir name.
    artifact_type
        Optional explicit artifact type (``--artifact-type``) —
        validated through the #394 two-tier registry. Defaults to the
        inferred ``report`` WITH a ``TODO(operator)`` marker.
    """
    directory = Path(directory).resolve()
    if not directory.is_dir():
        raise AdoptVnError(
            f"--adopt-vn target {directory} does not exist or is not a "
            f"directory."
        )

    # ---- family scan (refusals fire before any slug/project work so
    # the operator sees grammar problems first) --------------------------
    versions, sidecars, minors, strays = _scan_family(directory)
    if minors:
        _refuse_minors(minors, versions)

    # ---- project + BRIEF-mode resolution -------------------------------
    project_dir, brief_exists = _resolve_enclosing_project(directory)

    # ---- slug -----------------------------------------------------------
    if slug is not None:
        try:
            validate_explicit_slug(slug)
        except EnrollError as exc:
            raise AdoptVnError(str(exc)) from exc
    else:
        slug = _sanitize_default_slug(directory.name)

    adopt_plan = Plan(project_dir=project_dir, shape=Shape.ADOPT_VN)
    adopt_plan.brief_mode = "append" if brief_exists else "render"
    adopt_plan.synthesize_brief = not brief_exists

    if not versions:
        # Empty dir / already-adopted family: no-op plan (idempotence).
        return adopt_plan

    # ---- existing-BRIEF validation + collision checks -------------------
    existing_slugs: List[str] = []
    if brief_exists:
        try:
            existing_slugs = _check_existing_brief(project_dir)
        except EnrollError as exc:
            raise AdoptVnError(str(exc)) from exc
    else:
        # Creating a fresh BRIEF: pre-existing thread-shaped dirs would
        # be unlisted in the synthesized BRIEF and fail validation
        # (the enroll precedent).
        other_threads = sorted(
            d for d in _thread_shaped_dirs(project_dir) if d != slug
        )
        if other_threads:
            raise AdoptVnError(
                f"Project root {project_dir} has no BRIEF but contains "
                f"thread-shaped directories: {other_threads}. Suggested "
                f"fix: run /anvil:project-migrate {project_dir} first "
                f"to generate a BRIEF covering them, then re-run "
                f"--adopt-vn."
            )
    adopt_plan.preexisting_brief_slugs = list(existing_slugs)

    if slug in existing_slugs:
        raise AdoptVnError(
            f"Slug collision: `{slug}` is already listed in "
            f"{project_dir / BRIEF_FILENAME}. Suggested fix: pass "
            f"--slug with a different name."
        )

    target_dir = project_dir / slug
    if target_dir != directory and target_dir.exists():
        raise AdoptVnError(
            f"Slug collision: target directory {target_dir} already "
            f"exists and is not the vN family dir itself. Suggested "
            f"fix: pass --slug with a different name."
        )

    # ---- renames (versions ascending; sidecars ride with their dir) -----
    renames: List[Rename] = []
    for n in sorted(versions):
        version_target = target_dir / f"{slug}.{n}"
        if version_target.exists():
            raise AdoptVnError(
                f"Target collision: {version_target} already exists "
                f"(would clobber it when renaming `v{n}/`). Resolve "
                f"the collision manually, then re-run --adopt-vn. "
                f"Nothing was modified."
            )
        renames.append(Rename(source=versions[n], target=version_target))
        for tag, sidecar_dir in sorted(sidecars.get(n, [])):
            if _FOREIGN_TAG_SUFFIX_RE.search(tag):
                raise AdoptVnError(
                    f"Sidecar `{sidecar_dir.name}/` carries a versioned "
                    f"critic tag (`{tag}`) — renaming it would re-create "
                    f"a foreign name under the adopted stem. Tag "
                    f"vocabulary mapping (--tag-map) is Phase 2 of "
                    f"issue #432; Phase 1 refuses. Nothing was modified."
                )
            sidecar_target = target_dir / f"{slug}.{n}.{tag}"
            if sidecar_target.exists():
                raise AdoptVnError(
                    f"Target collision: {sidecar_target} already "
                    f"exists (would clobber it when renaming "
                    f"`{sidecar_dir.name}/`). Resolve the collision "
                    f"manually, then re-run --adopt-vn. Nothing was "
                    f"modified."
                )
            renames.append(
                Rename(source=sidecar_dir, target=sidecar_target)
            )

    # ---- artifact type ---------------------------------------------------
    if artifact_type is not None:
        try:
            doc_artifact_type = _validate_artifact_type_choice(
                artifact_type, project_dir
            )
        except EnrollError as exc:
            raise AdoptVnError(str(exc)) from exc
        inferred = False
        todo: Optional[str] = None
    else:
        doc_artifact_type = _DEFAULT_ADOPT_ARTIFACT_TYPE
        inferred = True
        todo = (
            "TODO(operator): confirm — inferred 'report' (vN report-dir "
            "adoption default)"
        )

    # ---- document plan ----------------------------------------------------
    version_nums = sorted(versions)
    sidecar_count = sum(len(v) for v in sidecars.values())
    doc = DocumentPlan(
        slug=slug,
        source_dir=directory,
        target_dir=target_dir,
        renames=renames,
        brief_merge=BriefMergeOp(
            slug=slug,
            artifact_type=doc_artifact_type,
            inferred=inferred,
            todo_comment=todo,
            slug_comment=f"adopted-from: {directory.name}/vN (issue #432)",
        ),
    )

    doc.notes.append(
        f"Adopt-vN: {len(version_nums)} version dirs "
        f"(v{version_nums[0]}..v{version_nums[-1]}) → `{slug}.{{N}}` "
        f"under `{target_dir.name}/`; {sidecar_count} critic sidecar(s) "
        f"renamed alongside."
    )
    gaps = sorted(
        set(range(version_nums[0], version_nums[-1] + 1)) - set(version_nums)
    )
    if gaps:
        doc.notes.append(
            f"Version gaps tolerated (per #408): missing "
            f"{', '.join(f'v{g}' for g in gaps)}."
        )
    for name in strays:
        doc.notes.append(
            f"Stray non-versioned dir left untouched: `{name}/` "
            f"(not part of the v{{N}} family grammar)."
        )
    bodies = _observed_body_filenames([versions[n] for n in version_nums])
    if bodies:
        doc.notes.append(
            "Observed body files recorded, never renamed (the #408 "
            "carve-out — dir-level renames move them along): "
            + ", ".join(f"`{b}`" for b in bodies)
            + "."
        )
    if inferred:
        doc.notes.append(
            f"{slug}: artifact_type inferred as '{doc_artifact_type}' — "
            f"confirm in BRIEF (TODO marker emitted)."
        )
        doc.operator_todos.append(
            f"`{slug}`: confirm `artifact_type: {doc_artifact_type}` "
            f"(inferred by vN report-dir adoption)."
        )

    log_line = (
        f"adopted vN report dirs from `{directory.name}/` as "
        f"`{slug}.{{N}}` (versions "
        f"{', '.join(f'v{n}' for n in version_nums)}; "
        f"{sidecar_count} critic sidecar(s) renamed alongside)"
    )
    doc.enrollment_log.append(log_line)

    adopt_plan.documents.append(doc)
    return adopt_plan


__all__ = [
    "AdoptVnError",
    "build_adopt_vn_plan",
]
