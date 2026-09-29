"""Letter-family adoption planning for `anvil:project-migrate` (issue #440).

Adopts foreign ``{Project}.{Letter}.{N}`` version-dir families (the
sphere-survey ip-thread grammar: ``Meridian.C.7/`` +
``Meridian.C.7.enablement/`` critic siblings, flat under one directory)
into the canonical anvil shape: ``<dir>/<slug>/<slug>.{N}/`` with
``<slug>.{N}.<tag>`` critic siblings, where the slug derives from the
``{Project}.{Letter}`` stem (``Meridian.C`` → ``meridian-c``).

Phase 2 of the issue #432 foreign-grammar adoption arc (Phase 1 =
``--adopt-vn``, PR #439; Phase 3 = single-file ``review.md`` conversion,
issue #454). Mirrors :mod:`adopt_vn` exactly in architecture: pure
planner, plan-mode :data:`detect.Shape.ADOPT_FAMILY` tag, reuse of the
:class:`plan.DocumentPlan` / :class:`plan.Rename` /
:class:`plan.BriefMergeOp` machinery, enroll-style BRIEF write dispatch.

Design notes
------------

- **Pure planner — no mutations.** Reads the tree (and the tag-map
  file) but never writes. The dry-run contract depends on it.
- **One invocation = one directory = N letter families (batch).** Each
  ``{Project}.{Letter}`` stem becomes ONE :class:`plan.DocumentPlan`
  with its own derived slug and BRIEF entry. Any plan-time error aborts
  the WHOLE batch before any mutation (the batch-enroll contract reused
  by ``--adopt-vn``).
- **Slugs are derived, not flagged.** There is deliberately NO
  ``--slug`` for this mode — multi-family invocations make a single
  override meaningless, and derived slugs are deterministic
  (lowercase; collapse non-alphanumeric runs to ``-``; trim). Slug
  collisions (BRIEF entry, on-disk dir, cross-family after
  sanitization) are plan-time refusals.
- **Declarative tag mapping — NO heuristics, ever (issue #432
  curation, "Declarative tag-mapping contract").** The foreign critic
  sidecar vocabulary (``.enablement``, ``.pre_flight``, ``.s101``,
  ``.fto``, ``.critic``, ``.audit2``, versioned tags like
  ``.review-v2``) maps through an operator-confirmed JSON table
  (``--tag-map <file>``, shape ``{"tag_map": {"<foreign>":
  "<canonical>", ...}}``; stdlib-only, the ``.anvil.json`` precedent):

  - REQUIRED whenever any critic sidecar that would be renamed is
    observed; every such observed tag MUST have an entry (identity
    mappings allowed and expected — ``s101: s101``);
  - an unmapped observed tag is a plan-time refusal LISTING the
    missing tags (the operator's next edit is mechanical);
  - values must satisfy the canonical tag grammar: a single dot-free
    word (``^[A-Za-z_][A-Za-z0-9_-]*$``) with no ``-vN`` suffix — i.e.
    they must NOT re-create a foreign name under the adopted stem
    (project-scout predicate iii) and must survive
    ``discover_critics``' single-segment tag rule;
  - two foreign tags resolving to ONE canonical tag on the SAME
    version dir (e.g. ``.audit`` + ``.audit2`` → ``audit`` on
    ``Meridian.C.7``) is a plan-time refusal; the same pair on
    DIFFERENT version dirs is legal;
  - the dry-run report prints the full per-directory resolution
    (every sidecar's old name → new name) for operator confirmation.

- **``--artifact-type`` is REQUIRED, invocation-wide.** Unlike
  ``--adopt-vn`` (report dirs → ``report`` is a safe inferred
  default), there is NO safe inference between ``ip-uspto`` (a full
  application) and ``ip-uspto-provisional`` (a provisional) — guessing
  would violate the nothing-is-guessed-silently discipline with real
  legal-artifact stakes. The value applies to every family in the
  invocation; each BRIEF entry carries a ``TODO(operator)`` marker, and
  per-family divergence is a documented post-adopt BRIEF edit.
- **Bodies are never renamed.** Observed body files inside the version
  dirs are recorded with a deferral note — the #408 carve-out applies
  verbatim (the dir-level rename moves them along).
- **Single-file ``review.md`` payloads stay invisible-but-intact.**
  Tag mapping governs the sidecar's NAME; the content conversion to a
  recognizable review payload is Phase 3 (issue #454). A renamed
  sidecar holding only ``review.md`` fails
  ``critics._has_recognizable_review`` and stays undiscovered by
  ``discover_critics`` (the #346 additive contract).
- **Idempotence.** Re-running on an adopted tree finds no letter
  family and yields an empty (no-op) plan.

Public API
----------

- ``AdoptFamilyError`` — typed plan-time refusal (a ``ValueError``).
- ``load_tag_map(path)`` — parse + shape-validate the tag-map JSON.
- ``build_adopt_family_plan(directory, ...)`` — top-level entry;
  returns a :class:`plan.Plan` (with ``plan.tag_resolution`` /
  ``plan.family_strays`` report-surface attributes).
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .adopt_vn import _FOREIGN_TAG_SUFFIX_RE, _format_ambiguous_slot
from .detect import (
    BRIEF_FILENAME,
    COUNSEL_MEMO_FILENAME,
    PROVISIONAL_BODY_FILENAME,
    Shape,
    has_counsel_memo_companion,
    has_native_provisional_body,
)
from .enroll import (
    EnrollError,
    _check_existing_brief,
    _thread_shaped_dirs,
    _validate_artifact_type_choice,
)
from .plan import BriefMergeOp, DocumentPlan, Plan, Rename


class AdoptFamilyError(ValueError):
    """Plan-time adoption refusal.

    Raised BEFORE any mutation — the whole batch (every letter family
    in the directory) aborts on the first plan-time error.
    """


# The foreign letter-family version-dir grammar: `{Project}.{Letter}.{N}`
# where `{Letter}` is the SINGLE-letter final dot-segment of the stem
# (`Meridian.C.7` → stem `Meridian.C`, N=7). The project part may itself
# contain dots (greedy) — the stem is everything up to and including the
# final single-letter segment.
_FAMILY_VERSION_RE = re.compile(r"^(?P<stem>.+\.[A-Za-z])\.(?P<num>\d+)$")

# A `{stem}.{N}.<tag>` critic sidecar (observed vocabulary:
# `.enablement`, `.pre_flight`, `.s101`, `.fto`, `.critic`, `.audit2`,
# `.review-v2`). The tag must start with a non-digit so a
# minor-versioned oddball (`Meridian.C.7.1`) cannot false-match as a
# sidecar with tag "1" — such names match neither regex and are
# reported as strays.
_FAMILY_SIDECAR_RE = re.compile(
    r"^(?P<stem>.+\.[A-Za-z])\.(?P<num>\d+)\.(?P<tag>[A-Za-z_].*)$"
)

# The canonical critic-tag grammar a tag-map VALUE must satisfy: a
# single dot-free word. Dots would break `discover_critics`'
# single-segment tag rule (anvil/lib/critics.py); the `-vN` suffix is
# checked separately (it would re-fire project-scout's foreign guard,
# predicate iii).
_CANONICAL_TAG_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*$")

# The top-level JSON key of the tag-map file.
_TAG_MAP_KEY = "tag_map"

# The two likely candidates named by the missing-artifact-type refusal
# (the consumer's letter families are ip threads — issue #440 curation).
_LIKELY_IP_TYPES = ("ip-uspto", "ip-uspto-provisional")

# The invocation-wide operator-confirmation marker (issue #440
# curation): the artifact type is operator-supplied but applied to
# EVERY family in the invocation, so each BRIEF entry asks for
# per-family confirmation.
_INVOCATION_WIDE_TODO = (
    "TODO(operator): confirm — applied invocation-wide by --adopt-family"
)

# Body-ish files recorded (never renamed — the #408 carve-out).
_OBSERVED_BODY_SUFFIXES = (".md", ".tex")


def _sanitize_family_slug(stem: str) -> str:
    """Fold a ``{Project}.{Letter}`` stem into a canonical slug.

    Same sanitization as :func:`adopt_vn._sanitize_default_slug`
    (lowercase; collapse non-alphanumeric runs to ``-``; trim):
    ``Meridian.C`` → ``meridian-c``. An empty result is a hard error —
    there is no ``--slug`` escape hatch in this mode (derived slugs
    only), so the operator must rename the family manually first.
    """
    slug = re.sub(r"[^a-z0-9]+", "-", stem.lower()).strip("-")
    if not slug:
        raise AdoptFamilyError(
            f"Could not derive a slug from family stem {stem!r} "
            f"(nothing left after sanitization). --adopt-family has no "
            f"--slug override (slugs are derived per family); rename "
            f"the family dirs manually, then re-run."
        )
    return slug


def load_tag_map(path: Path) -> Dict[str, str]:
    """Load + shape-validate the ``--tag-map`` JSON file.

    Returns the foreign→canonical mapping. Every failure is a typed
    plan-time refusal: unreadable file, invalid JSON, missing/non-dict
    ``"tag_map"`` key, non-string entries. VALUE-grammar validation
    (canonical tag rules) also happens here so a malformed map refuses
    even before the tree scan results are consulted.
    """
    path = Path(path)
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AdoptFamilyError(
            f"Cannot read --tag-map file {path}: {exc}"
        ) from exc
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        raise AdoptFamilyError(
            f"--tag-map file {path} is not valid JSON: {exc}"
        ) from exc
    if not isinstance(data, dict) or _TAG_MAP_KEY not in data:
        raise AdoptFamilyError(
            f"--tag-map file {path} must be a JSON object with a "
            f"top-level {_TAG_MAP_KEY!r} key: "
            f'{{"{_TAG_MAP_KEY}": {{"<foreign>": "<canonical>", ...}}}}.'
        )
    mapping = data[_TAG_MAP_KEY]
    if not isinstance(mapping, dict):
        raise AdoptFamilyError(
            f"--tag-map file {path}: {_TAG_MAP_KEY!r} must be a JSON "
            f"object mapping foreign tags to canonical tags."
        )
    out: Dict[str, str] = {}
    bad_values: List[str] = []
    for key, value in mapping.items():
        if not isinstance(key, str) or not isinstance(value, str):
            raise AdoptFamilyError(
                f"--tag-map file {path}: every {_TAG_MAP_KEY!r} entry "
                f"must map a string foreign tag to a string canonical "
                f"tag (offending entry: {key!r}: {value!r})."
            )
        if (
            not _CANONICAL_TAG_RE.match(value)
            or _FOREIGN_TAG_SUFFIX_RE.search(value)
        ):
            bad_values.append(f"`{key}` → `{value}`")
        out[key] = value
    if bad_values:
        raise AdoptFamilyError(
            f"--tag-map file {path} maps to non-canonical tag value(s): "
            + ", ".join(bad_values)
            + ". A canonical critic tag is a single dot-free word "
            "(`^[A-Za-z_][A-Za-z0-9_-]*$`) with no `-vN` suffix. "
            "Nothing was modified."
        )
    return out


def _scan_families(
    directory: Path,
) -> Tuple[
    Dict[str, Dict[int, Path]],
    Dict[str, Dict[int, List[Tuple[str, Path]]]],
    Dict[str, List[str]],
    List[str],
]:
    """Scan ``directory`` for letter families.

    Returns ``(families, sidecars, orphans, strays)`` where
    ``families`` maps stem → {N → version dir}, ``sidecars`` maps
    stem → {N → [(foreign_tag, dir), ...]}, ``orphans`` maps stem →
    sidecar dir names whose version dir is absent (untouched,
    reported per family), and ``strays`` lists directory names that
    match neither grammar (untouched, reported once).

    A version slot or sidecar ``(stem, N, tag)`` slot claimed by more
    than one directory name (the leading-zero collapse, issue #458:
    ``Meridian.C.07/`` + ``Meridian.C.7/``) is a scan-time refusal —
    the whole batch aborts BEFORE any slug/BRIEF/collision work,
    naming every colliding dir per slot.
    """
    version_claims: Dict[Tuple[str, int], List[Path]] = {}
    sidecar_claims: Dict[Tuple[str, int, str], List[Path]] = {}
    strays: List[str] = []

    try:
        children = sorted(directory.iterdir())
    except OSError as exc:
        raise AdoptFamilyError(
            f"Cannot read directory {directory}: {exc}"
        ) from exc

    for child in children:
        if not child.is_dir():
            continue  # Loose files stay where they are; not family grammar.
        name = child.name
        m = _FAMILY_SIDECAR_RE.match(name)
        if m is not None:
            sidecar_claims.setdefault(
                (m.group("stem"), int(m.group("num")), m.group("tag")), []
            ).append(child)
            continue
        m = _FAMILY_VERSION_RE.match(name)
        if m is not None:
            version_claims.setdefault(
                (m.group("stem"), int(m.group("num"))), []
            ).append(child)
            continue
        strays.append(name)

    ambiguous: List[str] = []
    families: Dict[str, Dict[int, Path]] = {}
    for stem, num in sorted(version_claims):
        claimants = version_claims[(stem, num)]
        if len(claimants) > 1:
            ambiguous.append(
                _format_ambiguous_slot(
                    [c.name for c in claimants],
                    f"`{stem}` version {num}",
                )
            )
        else:
            families.setdefault(stem, {})[num] = claimants[0]

    stems_with_versions = {stem for stem, _ in version_claims}
    sidecars: Dict[str, Dict[int, List[Tuple[str, Path]]]] = {}
    orphans: Dict[str, List[str]] = {}
    for stem, num, tag in sorted(sidecar_claims):
        claimants = sidecar_claims[(stem, num, tag)]
        if (stem, num) in version_claims:
            if len(claimants) > 1:
                ambiguous.append(
                    _format_ambiguous_slot(
                        [c.name for c in claimants],
                        f"the `{stem}` version-{num} `{tag}` sidecar",
                    )
                )
                continue
            sidecars.setdefault(stem, {}).setdefault(num, []).append(
                (tag, claimants[0])
            )
        elif stem in stems_with_versions:
            # Orphan sidecar(s) (family exists, version dir absent) —
            # untouched, reported on the family.
            orphans.setdefault(stem, []).extend(
                c.name for c in claimants
            )
        else:
            # Sidecar(s) of a stem with no version dirs at all — stray.
            strays.extend(c.name for c in claimants)

    if ambiguous:
        raise AdoptFamilyError(
            "Ambiguous version numbering: "
            + "; ".join(ambiguous)
            + " — rename one of each colliding set manually, then "
            "re-run --adopt-family. Nothing was modified."
        )

    return families, sidecars, orphans, sorted(strays)


def _observed_tags(
    sidecars: Dict[str, Dict[int, List[Tuple[str, Path]]]],
) -> List[str]:
    """Collect the distinct foreign tags across every renameable sidecar."""
    seen: set = set()
    for per_version in sidecars.values():
        for entries in per_version.values():
            for tag, _ in entries:
                seen.add(tag)
    return sorted(seen)


def _check_tag_map_against_observed(
    tag_map: Optional[Dict[str, str]],
    sidecars: Dict[str, Dict[int, List[Tuple[str, Path]]]],
) -> Dict[str, str]:
    """Validate the tag map against the observed sidecar vocabulary.

    All refusals are plan-time: missing ``--tag-map`` when sidecars
    exist; unmapped observed tags (listed); two foreign tags resolving
    to one canonical tag on the SAME version dir.
    """
    observed = _observed_tags(sidecars)
    if not observed:
        # Sidecar-free invocation: --tag-map is optional.
        return tag_map or {}
    if tag_map is None:
        raise AdoptFamilyError(
            "Critic sidecars observed but no --tag-map was passed. "
            "--adopt-family never guesses tag vocabulary — pass "
            "--tag-map <file> with a JSON object mapping every "
            "observed foreign tag to a canonical tag. Observed tags: "
            + ", ".join(f"`{t}`" for t in observed)
            + ". Nothing was modified."
        )
    missing = sorted(set(observed) - set(tag_map))
    if missing:
        raise AdoptFamilyError(
            "Unmapped foreign sidecar tag(s) — every observed tag must "
            "have a --tag-map entry (identity mappings are allowed): "
            + ", ".join(f"`{t}`" for t in missing)
            + ". Add the missing entries to the tag-map file, then "
            "re-run. Nothing was modified."
        )
    # Same-dir collision: two foreign tags → one canonical tag on one
    # version dir. The same pair on different version dirs is legal.
    for stem in sorted(sidecars):
        for num in sorted(sidecars[stem]):
            resolved: Dict[str, str] = {}
            for tag, _ in sorted(sidecars[stem][num]):
                canonical = tag_map[tag]
                if canonical in resolved:
                    raise AdoptFamilyError(
                        f"Tag-map collision on `{stem}.{num}`: foreign "
                        f"tags `{resolved[canonical]}` and `{tag}` both "
                        f"resolve to canonical tag `{canonical}` on the "
                        f"same version dir — the renamed siblings would "
                        f"collide. Map one of them to a different "
                        f"canonical tag. Nothing was modified."
                    )
                resolved[canonical] = tag
    return tag_map


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


def build_adopt_family_plan(
    directory: Path,
    *,
    tag_map_path: Optional[Path] = None,
    artifact_type: Optional[str] = None,
) -> Plan:
    """Build a letter-family adoption :class:`plan.Plan` for ``directory``.

    Every check here is plan-time (pre-mutation); any failure raises
    :class:`AdoptFamilyError` and aborts the WHOLE batch before
    anything is moved. A directory with no letter family yields an
    EMPTY plan (``plan.is_noop``) — re-running on an adopted tree is a
    no-op, not an error.

    The returned plan carries two report-surface attributes consumed by
    the orchestrate formatter:

    - ``plan.tag_resolution`` — ``[(slug, old_sidecar_name,
      new_sidecar_name), ...]`` (the full per-directory resolution the
      operator confirms before ``--apply``);
    - ``plan.family_strays`` — directory names left untouched at the
      family root.

    Parameters
    ----------
    directory
        The directory holding the flat ``{Project}.{Letter}.{N}``
        dirs. It is the project root: adopted families land at
        ``<directory>/<slug>/<slug>.{N}`` and the BRIEF lives at
        ``<directory>/BRIEF.md`` (surgically appended when it already
        exists; synthesized otherwise).
    tag_map_path
        Path to the ``--tag-map`` JSON file. REQUIRED whenever any
        renameable critic sidecar is observed; optional for
        sidecar-free families.
    artifact_type
        REQUIRED (``--artifact-type``) — validated through the #394
        two-tier registry and applied invocation-wide with a
        per-family ``TODO(operator)`` marker. There is no inferred
        default in this mode.
    """
    directory = Path(directory).resolve()
    if not directory.is_dir():
        raise AdoptFamilyError(
            f"--adopt-family target {directory} does not exist or is "
            f"not a directory."
        )

    # ---- family scan (grammar problems surface first) -------------------
    families, sidecars, orphans, strays = _scan_families(directory)

    # The family dir IS the project root in this mode: families sit
    # flat under it and the canonical target is `<dir>/<slug>/<slug>.N`
    # (post-write strict validation requires the slug dirs directly
    # under the BRIEF-bearing root). `brief_exists` keys on FILE
    # existence (the adopt-vn precedent), not parseability — an
    # unparseable BRIEF.md must route through `_check_existing_brief`'s
    # refusal, never silently into the synthesis (overwrite) path.
    project_dir = directory
    brief_exists = (project_dir / BRIEF_FILENAME).is_file()

    adopt_plan = Plan(project_dir=project_dir, shape=Shape.ADOPT_FAMILY)
    adopt_plan.brief_mode = "append" if brief_exists else "render"
    adopt_plan.synthesize_brief = not brief_exists
    adopt_plan.tag_resolution = []  # type: ignore[attr-defined]
    adopt_plan.family_strays = []  # type: ignore[attr-defined]

    if not families:
        # Empty dir / already-adopted tree: no-op plan (idempotence).
        return adopt_plan
    adopt_plan.family_strays = list(strays)  # type: ignore[attr-defined]

    # ---- tag-map contract (issue #432 curation, pinned by #440) ---------
    tag_map: Optional[Dict[str, str]] = None
    if tag_map_path is not None:
        tag_map = load_tag_map(tag_map_path)
    tag_map = _check_tag_map_against_observed(tag_map, sidecars)

    # ---- artifact type: REQUIRED, invocation-wide ------------------------
    if artifact_type is None:
        candidates = " / ".join(f"`{t}`" for t in _LIKELY_IP_TYPES)
        raise AdoptFamilyError(
            "--artifact-type is required for --adopt-family: there is "
            "no safe inference between a full application and a "
            f"provisional (likely candidates: {candidates}). The value "
            "applies to every family in the invocation; per-family "
            "divergence is a post-adopt BRIEF edit. Nothing was "
            "modified."
        )
    try:
        doc_artifact_type = _validate_artifact_type_choice(
            artifact_type, project_dir
        )
    except EnrollError as exc:
        raise AdoptFamilyError(str(exc)) from exc

    # ---- slugs: derived per family; collisions refuse --------------------
    slug_by_stem: Dict[str, str] = {}
    stems_by_slug: Dict[str, List[str]] = {}
    for stem in sorted(families):
        slug = _sanitize_family_slug(stem)
        slug_by_stem[stem] = slug
        stems_by_slug.setdefault(slug, []).append(stem)
    for slug, stems in sorted(stems_by_slug.items()):
        if len(stems) > 1:
            raise AdoptFamilyError(
                f"Cross-family slug collision: stems "
                + ", ".join(f"`{s}`" for s in stems)
                + f" all sanitize to slug `{slug}`. --adopt-family has "
                f"no --slug override; rename one family manually, then "
                f"re-run. Nothing was modified."
            )

    # ---- existing-BRIEF validation + collision checks --------------------
    existing_slugs: List[str] = []
    if brief_exists:
        try:
            existing_slugs = _check_existing_brief(project_dir)
        except EnrollError as exc:
            raise AdoptFamilyError(str(exc)) from exc
    else:
        # Creating a fresh BRIEF: pre-existing thread-shaped dirs would
        # be unlisted in the synthesized BRIEF and fail validation
        # (the enroll / adopt-vn precedent).
        other_threads = sorted(
            d
            for d in _thread_shaped_dirs(project_dir)
            if d not in stems_by_slug
        )
        if other_threads:
            raise AdoptFamilyError(
                f"Project root {project_dir} has no BRIEF but contains "
                f"thread-shaped directories: {other_threads}. Suggested "
                f"fix: run /anvil:project-migrate {project_dir} first "
                f"to generate a BRIEF covering them, then re-run "
                f"--adopt-family."
            )
    adopt_plan.preexisting_brief_slugs = list(existing_slugs)

    # ---- per-family document plans ---------------------------------------
    for stem in sorted(families):
        slug = slug_by_stem[stem]
        if slug in existing_slugs:
            raise AdoptFamilyError(
                f"Slug collision: `{slug}` (derived from `{stem}`) is "
                f"already listed in {project_dir / BRIEF_FILENAME}. "
                f"Rename the family manually, then re-run. Nothing was "
                f"modified."
            )
        target_dir = project_dir / slug
        if target_dir.exists():
            raise AdoptFamilyError(
                f"Slug collision: target directory {target_dir} "
                f"(derived from `{stem}`) already exists. Rename the "
                f"family manually, then re-run. Nothing was modified."
            )

        versions = families[stem]
        version_nums = sorted(versions)

        # Counsel-memo-only refusal (issue #503, shared rule): a family
        # whose version dirs carry `counsel_memo.tex` but NO
        # `provisional.tex` is not a fileable body — a counsel memo is a
        # finalize-output companion. Refuse before any mutation (the
        # whole batch aborts; nothing is touched).
        family_bodies = _observed_body_filenames(
            [versions[n] for n in version_nums]
        )
        if has_counsel_memo_companion(
            family_bodies
        ) and not has_native_provisional_body(family_bodies):
            raise AdoptFamilyError(
                f"Letter family `{stem}` carries `{COUNSEL_MEMO_FILENAME}` "
                f"but no `{PROVISIONAL_BODY_FILENAME}`. A counsel memo is "
                f"a finalize-output companion (anvil writes it into "
                f"`<thread>.counsel/`), not a fileable provisional body. "
                f"Suggested fix: add the `{PROVISIONAL_BODY_FILENAME}` "
                f"body this counsel memo accompanies, then re-run. "
                f"Nothing was modified."
            )

        renames: List[Rename] = []
        resolution: List[Tuple[str, str, str]] = []
        sidecar_count = 0
        for n in version_nums:
            version_target = target_dir / f"{slug}.{n}"
            if version_target.exists():
                raise AdoptFamilyError(
                    f"Target collision: {version_target} already exists "
                    f"(would clobber it when renaming `{stem}.{n}/`). "
                    f"Resolve the collision manually, then re-run. "
                    f"Nothing was modified."
                )
            renames.append(Rename(source=versions[n], target=version_target))
            seen_targets: set = set()
            for tag, sidecar_dir in sorted(
                sidecars.get(stem, {}).get(n, [])
            ):
                canonical = tag_map[tag]
                sidecar_target = target_dir / f"{slug}.{n}.{canonical}"
                if sidecar_target.exists():
                    raise AdoptFamilyError(
                        f"Target collision: {sidecar_target} already "
                        f"exists (would clobber it when renaming "
                        f"`{sidecar_dir.name}/`). Resolve the collision "
                        f"manually, then re-run. Nothing was modified."
                    )
                if sidecar_target.name in seen_targets:
                    # Backstop only (#458): duplicate sidecar slots and
                    # same-dir tag-map collisions both refuse earlier,
                    # at scan / tag-map time.
                    raise AdoptFamilyError(
                        f"In-plan target collision: two sidecars of "
                        f"`{stem}.{n}` would both rename to "
                        f"{sidecar_target} (renaming "
                        f"`{sidecar_dir.name}/` collides with an "
                        f"already-planned rename). Resolve the "
                        f"ambiguity manually, then re-run. Nothing was "
                        f"modified."
                    )
                seen_targets.add(sidecar_target.name)
                renames.append(
                    Rename(source=sidecar_dir, target=sidecar_target)
                )
                resolution.append(
                    (slug, sidecar_dir.name, sidecar_target.name)
                )
                sidecar_count += 1

        doc = DocumentPlan(
            slug=slug,
            source_dir=directory,
            target_dir=target_dir,
            renames=renames,
            brief_merge=BriefMergeOp(
                slug=slug,
                artifact_type=doc_artifact_type,
                inferred=False,
                todo_comment=_INVOCATION_WIDE_TODO,
                slug_comment=(
                    f"adopted-from: {stem}.{{N}} (issue #440)"
                ),
            ),
        )

        doc.notes.append(
            f"Adopt-family: {len(version_nums)} version dirs "
            f"(`{stem}.{version_nums[0]}`..`{stem}.{version_nums[-1]}`) "
            f"→ `{slug}.{{N}}` under `{slug}/`; {sidecar_count} critic "
            f"sidecar(s) renamed alongside per the tag map."
        )
        gaps = sorted(
            set(range(version_nums[0], version_nums[-1] + 1))
            - set(version_nums)
        )
        if gaps:
            doc.notes.append(
                f"Version gaps tolerated (per #408): missing "
                + ", ".join(f"`{stem}.{g}`" for g in gaps)
                + "."
            )
        for orphan_name in sorted(orphans.get(stem, [])):
            doc.notes.append(
                f"Orphan sidecar left untouched: `{orphan_name}/` (its "
                f"version dir is absent)."
            )
        bodies = _observed_body_filenames(
            [versions[n] for n in version_nums]
        )
        if bodies:
            doc.notes.append(
                "Observed body files recorded, never renamed (the #408 "
                "carve-out — dir-level renames move them along): "
                + ", ".join(f"`{b}`" for b in bodies)
                + "."
            )
        # Counsel-memo companion preservation (issue #503): when a
        # `provisional.tex` body and a `counsel_memo.tex` coexist, the
        # provisional is the body and the counsel memo is a PRESERVED
        # COMPANION (never the body, never renamed).
        if has_native_provisional_body(bodies) and has_counsel_memo_companion(
            bodies
        ):
            doc.notes.append(
                f"{slug}: {COUNSEL_MEMO_FILENAME} preserved as a companion "
                f"alongside {PROVISIONAL_BODY_FILENAME} (a finalize-output "
                f"counsel memo, never a version-dir body) — recorded, "
                f"never selected as the body, never renamed."
            )
        doc.notes.append(
            f"{slug}: artifact_type `{doc_artifact_type}` applied "
            f"invocation-wide by --adopt-family — confirm per family in "
            f"the BRIEF (TODO marker emitted)."
        )
        doc.operator_todos.append(
            f"`{slug}`: confirm `artifact_type: {doc_artifact_type}` "
            f"(applied invocation-wide by --adopt-family)."
        )
        doc.enrollment_log.append(
            f"adopted letter family `{stem}` as `{slug}.{{N}}` "
            f"(versions "
            + ", ".join(str(n) for n in version_nums)
            + f"; {sidecar_count} critic sidecar(s) renamed per the "
            f"tag map)"
        )

        adopt_plan.documents.append(doc)
        adopt_plan.tag_resolution.extend(resolution)  # type: ignore[attr-defined]

    return adopt_plan


__all__ = [
    "AdoptFamilyError",
    "build_adopt_family_plan",
    "load_tag_map",
]
