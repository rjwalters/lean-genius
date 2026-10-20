"""Migration plan generation for `anvil:project-migrate` (issue #297).

Takes a :class:`ProjectInventory` (from :mod:`detect`) and produces a
:class:`Plan` listing the per-document migration steps. The plan is the
single intermediate artifact between detection and apply — dry-run prints
it; apply executes it.

Design notes
------------

- **Pure planner — no mutations.** Like the detector, this module reads
  files but never writes. The dry-run contract depends on this: plan
  generation can run without touching disk.
- **One plan per project.** The plan groups per-document operations into a
  single object so the apply step has a single iteration target. Each
  ``DocumentPlan`` is independently applyable, which is the atomicity
  contract.
- **Content rewrites are explicit.** Cross-thread reference rewriting is
  recorded as ``ContentRewrite`` entries — the apply step does not need to
  re-scan files; it consumes the recorded rewrites directly. This keeps
  the plan reviewable: the operator can see in the dry-run output exactly
  which strings will be substituted in which files.

Public API
----------

- ``ContentRewrite`` — one in-file substitution.
- ``Rename`` — one filesystem rename (source → target).
- ``BriefMergeOp`` — one ``documents:`` entry to write into the project
  BRIEF.
- ``DocumentPlan`` — per-document plan.
- ``Plan`` — top-level plan covering the whole project.
- ``build_plan(project_dir, shape, inventory=None)`` — top-level entry.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .detect import (
    ANVIL_JSON_FILENAME,
    BRIEF_FILENAME,
    COUNSEL_MEMO_FILENAME,
    PROVISIONAL_BODY_FILENAME,
    ProjectInventory,
    Shape,
    ThreadInventory,
    _RETAINED_BODY_FILENAMES,
    _SKILL_FIXED_BODY_FILENAMES,
    has_counsel_memo_companion,
    has_native_provisional_body,
    inventory_project,
)


class PlanError(ValueError):
    """Plan-time migration refusal (a ``ValueError``).

    Raised BEFORE any mutation — planning is pure, so a refusal here
    leaves the tree byte-identical (the two-phase abort contract shared
    with :class:`enroll.EnrollError` / :class:`adopt_family.AdoptFamilyError`).
    Introduced for issue #503: a bare thread whose newest version dir
    carries ``counsel_memo.tex`` but no ``provisional.tex`` is a refusal
    (a counsel memo is a finalize-output companion, not a fileable body).
    """


def _validate_migrate_artifact_type(value: str, project_dir: Path) -> str:
    """Validate the main mode's ``--artifact-type`` (issue #878).

    Same two-tier contract as ``enroll._validate_artifact_type_choice``
    (Tier 1: :data:`anvil.lib.project_brief.REGISTERED_ARTIFACT_TYPES`;
    Tier 2: consumer-declared types via ``discover_consumer_artifact_types``).
    Duplicated locally rather than imported — ``enroll.py`` already imports
    from this module, so importing back would be circular. Guarded import:
    when ``anvil.lib`` is unavailable the value passes through unchanged
    (the post-write strict BRIEF parse is the backstop).
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
    raise PlanError(
        f"--artifact-type {value!r} is not a registered or "
        f"consumer-declared artifact type. Registered: "
        f"{list(REGISTERED_ARTIFACT_TYPES)}. Consumer-declared: "
        f"{sorted(consumer_types)}."
    )


# Artifact-type inference from retained body filenames (issue #386).
# A retained body identifies the owning skill, so the planner writes
# the matching skill-identity artifact_type (registered in
# ``anvil/lib/project_brief.py`` under #386) instead of silently
# defaulting to 'investment-memo'. ``deck.md`` is ambiguous between
# anvil:deck and anvil:slides (both use it) — the planner defaults to
# 'deck' and the inference note tells the operator to edit the BRIEF
# entry to 'slides' for talk decks.
_RETAINED_BODY_ARTIFACT_TYPES: Dict[str, str] = {
    "deck.md": "deck",
    "proposal.tex": "proposal",
}


# Cross-thread reference pattern. Looks for ``<stem>.<N>`` tokens that
# match a known stem on the project, so we can rewrite them to
# ``<slug>.<N>``.
def _cross_thread_ref_re(stems: List[str]) -> re.Pattern:
    """Build a regex matching any of the known stem.N tokens.

    Used to find cross-thread references in body markdown that need
    rewriting after the directory rename. We anchor with ``\\b`` on both
    sides so partial matches inside other tokens are excluded.
    """
    if not stems:
        # An impossible pattern that matches nothing.
        return re.compile(r"(?!.*)")
    escaped = "|".join(re.escape(stem) for stem in stems)
    return re.compile(rf"\b({escaped})\.(\d+)\b")


@dataclass
class ContentRewrite:
    """One in-file substitution.

    Attributes
    ----------
    file_path
        Absolute path to the file that will be rewritten. The path is the
        TARGET path (where the file will be after renames) so the apply
        step can sequence renames first, content rewrites second.
    old_string
        The literal string to find. Single occurrence per ``ContentRewrite``
        — multi-occurrence rewrites are recorded as multiple entries.
    new_string
        The literal replacement.
    occurrences
        Count of occurrences expected (for the report). Apply uses this to
        sanity-check the rewrite landed cleanly.
    """

    file_path: Path
    old_string: str
    new_string: str
    occurrences: int = 1


@dataclass
class Rename:
    """One filesystem rename (source → target).

    The plan emits renames in dependency order: a rename of ``A/B`` happens
    before a rename of ``A/B/C`` (so the inner path is correct after the
    outer rename). The apply step trusts the order.
    """

    source: Path
    target: Path


@dataclass
class BriefMergeOp:
    """One ``documents:`` entry to add or update in the project BRIEF.

    The apply step collects every ``BriefMergeOp`` across the plan, builds
    the final ``documents:`` list, and writes the project BRIEF in a
    single atomic step at the end.

    Attributes
    ----------
    slug
        The slug for this document.
    artifact_type
        Registered artifact type per ``project_brief.REGISTERED_ARTIFACT_TYPES``.
        Defaults to ``"investment-memo"`` (the most common shape, and the
        no-information fallback for memo-shaped threads). When the thread
        carries a retained body filename the planner overwrites the
        default with the inferred skill-identity type (``deck.md`` →
        ``deck``, ``proposal.tex`` → ``proposal`` — issue #386); the
        operator can edit the BRIEF after migration if the inference is
        wrong (e.g. ``slides`` for a ``deck.md``-bodied talk deck).
    target_length
        Optional ``[min_words, max_words]`` carried from a `.anvil.json`.
    target_length_overrides
        Optional per-version override map carried from a `.anvil.json`.
    rubric_overrides
        Optional rubric overrides block carried from a `.anvil.json`.
    max_iterations
        Optional iteration-cap override carried from a `.anvil.json`
        (issue #382 — the deck-skill paired-override carrier). Only
        carried when the paired contract holds (``>= 4`` with a
        non-empty rationale); see :func:`_extract_iteration_cap`.
    iteration_cap_rationale
        The paired rationale for ``max_iterations``. Always present when
        ``max_iterations`` is (the BRIEF parser rejects unbalanced
        pairs at parse time).
    inferred
        True when ``artifact_type`` was INFERRED from observed on-disk
        state rather than carried from legacy config (issue #408 —
        bare version-dir threads). Inferred values are proposals, not
        facts; the serializer pairs them with ``todo_comment``.
    todo_comment
        Operator-confirmation marker (issue #408). When set, the BRIEF
        serializer appends it as a YAML comment on the
        ``artifact_type:`` line (e.g. ``artifact_type: paper  # TODO...``).
        YAML comments are ignored by ``yaml.safe_load`` and harmless to
        the no-pyyaml hand parser, and survive idempotent re-runs
        byte-for-byte (the no-op path never rewrites the BRIEF). A
        future NON-noop rewrite would drop them — which is why the
        synthesized BRIEF also mirrors the TODO list into the body
        prose (preserved verbatim on rewrite).
    slug_comment
        Provenance marker for enrolled documents (issue #406). When
        set, the BRIEF serializer appends it as a YAML comment on the
        ``- slug:`` line (e.g. ``- slug: topic-a  # enrolled-from:
        2026-05-19-topic-a.md (date: 2026-05-19)``). Like
        ``todo_comment``, it is invisible to YAML parsers; the
        enrollment-log line in the BRIEF body mirrors the same
        provenance so it survives any future non-noop rewrite.
    """

    slug: str
    artifact_type: str = "investment-memo"
    target_length: Optional[Tuple[int, int]] = None
    target_length_overrides: Optional[Dict[str, Tuple[int, int]]] = None
    rubric_overrides: Optional[dict] = None
    max_iterations: Optional[int] = None
    iteration_cap_rationale: Optional[str] = None
    inferred: bool = False
    todo_comment: Optional[str] = None
    slug_comment: Optional[str] = None


@dataclass
class DocumentPlan:
    """Per-document migration plan.

    Atomic unit of the apply step. If applying this plan fails, the apply
    step rolls back THIS plan only.
    """

    slug: str
    source_dir: Path
    target_dir: Path
    renames: List[Rename] = field(default_factory=list)
    content_rewrites: List[ContentRewrite] = field(default_factory=list)
    brief_merge: Optional[BriefMergeOp] = None
    anvil_json_to_delete: Optional[Path] = None
    notes: List[str] = field(default_factory=list)
    # Operator-confirmation checklist items mirrored into the synthesized
    # BRIEF's body prose (issue #408). Body prose is preserved verbatim
    # on BRIEF rewrite, so these survive even a future non-noop rewrite
    # that drops the YAML comments.
    operator_todos: List[str] = field(default_factory=list)
    # Enrollment-log lines appended to the BRIEF body (issue #406).
    # Body prose survives any future BRIEF re-render verbatim, so the
    # provenance recorded here (original filename, stripped date) is
    # durable even though the matching YAML comments are not.
    enrollment_log: List[str] = field(default_factory=list)

    @property
    def is_noop(self) -> bool:
        """Return True when this plan is a no-op (the doc is already migrated)."""
        return (
            not self.renames
            and not self.content_rewrites
            and self.brief_merge is None
            and self.anvil_json_to_delete is None
        )


@dataclass
class Plan:
    """Top-level project migration plan.

    The plan composes per-document plans, the project-BRIEF write op, and
    a list of ``.anvil.json`` paths to delete after the per-doc applies.
    """

    project_dir: Path
    shape: Shape
    documents: List[DocumentPlan] = field(default_factory=list)
    project_brief_path: Path = field(init=False)
    # Slugs that appear in the existing project BRIEF but have no on-disk
    # thread (the planner leaves them in place; operator decides).
    preexisting_brief_slugs: List[str] = field(default_factory=list)
    extra_anvil_jsons_to_delete: List[Path] = field(default_factory=list)
    # True when the project is BARE (issue #408 — version-dir families
    # with no anvil config anywhere): the project BRIEF will be
    # SYNTHESIZED from observed state. The BRIEF serializer emits
    # operator-confirmation TODO comments on every defaulted /
    # inferred field when this is set. Automatic when the inventory's
    # ``is_bare`` predicate holds — there is nothing to merge from, so
    # synthesis is the only sane behavior and dry-run-by-default is
    # the safety surface (no extra CLI flag).
    synthesize_brief: bool = False
    # How the project BRIEF is written at apply time (issue #406).
    #
    # - ``"render"`` (default — preserves migrate behavior untouched):
    #   the BRIEF is re-rendered from parsed state via
    #   ``render_project_brief``.
    # - ``"append"``: the existing BRIEF text is extended by SURGICAL
    #   textual append — new ``documents:`` entries are inserted at the
    #   end of the existing ``documents:`` block and enrollment-log
    #   lines are appended to the body; every pre-existing byte
    #   (comments, ``theme:``, ``render_*`` keys, quoting, entry order)
    #   is preserved byte-identically. Used by the enroll planner when
    #   a project BRIEF already exists, because the re-render path is
    #   lossy (it drops top-level ``theme:``, per-doc ``render_*`` /
    #   ``latex_header_includes``, and every YAML comment).
    brief_mode: str = "render"

    def __post_init__(self) -> None:
        self.project_brief_path = self.project_dir / BRIEF_FILENAME

    @property
    def is_noop(self) -> bool:
        """Return True when the entire plan is a no-op (fully migrated already)."""
        return all(doc.is_noop for doc in self.documents) and (
            not self.extra_anvil_jsons_to_delete
        )


def _read_anvil_json(path: Path) -> dict:
    """Read a ``.anvil.json`` file; return an empty dict on any failure.

    Lenient: a malformed `.anvil.json` is recorded as a note rather than
    blocking the migration. The operator can fix the BRIEF after the fact.
    """
    try:
        text = path.read_text(encoding="utf-8")
        return json.loads(text)
    except (OSError, json.JSONDecodeError):
        return {}


def _extract_target_length(
    anvil_data: dict,
) -> Tuple[Optional[Tuple[int, int]], Optional[Dict[str, Tuple[int, int]]]]:
    """Pull target_length from a `.anvil.json` shape.

    Handles both flat (`target_length: {words: [...]}`) and extended
    (`target_length: {default: {...}, overrides: {...}}`) forms. Returns a
    pair of (flat-range, overrides-map) where either may be ``None``.
    """
    tl = anvil_data.get("target_length")
    if not isinstance(tl, dict):
        return None, None

    flat: Optional[Tuple[int, int]] = None
    overrides: Optional[Dict[str, Tuple[int, int]]] = None

    # Flat form: {"words": [min, max]} or {"pages": [min, max]}.
    if "words" in tl:
        rng = tl["words"]
        if isinstance(rng, list) and len(rng) == 2:
            try:
                flat = (int(rng[0]), int(rng[1]))
            except (TypeError, ValueError):
                pass
    elif "pages" in tl:
        rng = tl["pages"]
        if isinstance(rng, list) and len(rng) == 2:
            try:
                # Convert pages → words (600 wpp per SKILL.md convention).
                flat = (int(rng[0]) * 600, int(rng[1]) * 600)
            except (TypeError, ValueError):
                pass

    # Extended form: {"default": {...}, "overrides": {...}}.
    if "default" in tl and isinstance(tl["default"], dict):
        if "words" in tl["default"]:
            rng = tl["default"]["words"]
            if isinstance(rng, list) and len(rng) == 2:
                try:
                    flat = (int(rng[0]), int(rng[1]))
                except (TypeError, ValueError):
                    pass

    if "overrides" in tl and isinstance(tl["overrides"], dict):
        ov: Dict[str, Tuple[int, int]] = {}
        for key, val in tl["overrides"].items():
            # Normalize ``v1`` / ``v2`` / ``1`` / ``"1"`` to bare integer-string.
            if isinstance(key, str) and key.startswith("v"):
                norm_key = key[1:]
            else:
                norm_key = str(key)
            if not norm_key.isdigit():
                continue
            if isinstance(val, dict) and "words" in val:
                rng = val["words"]
                if isinstance(rng, list) and len(rng) == 2:
                    try:
                        ov[norm_key] = (int(rng[0]), int(rng[1]))
                    except (TypeError, ValueError):
                        pass
            elif isinstance(val, list) and len(val) == 2:
                try:
                    ov[norm_key] = (int(val[0]), int(val[1]))
                except (TypeError, ValueError):
                    pass
        if ov:
            overrides = ov

    return flat, overrides


def _extract_iteration_cap(
    anvil_data: dict,
) -> Tuple[Optional[int], Optional[str]]:
    """Pull the paired iteration-cap override from a `.anvil.json` shape.

    The deck skill's per-thread carrier (issue #382) pairs
    ``max_iterations`` with a required ``iteration_cap_rationale``. The
    project-BRIEF schema (`anvil/lib/project_brief.py`) enforces the
    same contract STRICTLY at parse time, so the planner only carries
    the pair into the BRIEF when it would survive that validation:

    - ``max_iterations`` is an int ``>= 4`` (the principled floor —
      ``project_brief.DEFAULT_MAX_ITERATIONS``), AND
    - ``iteration_cap_rationale`` is a non-empty string.

    Anything else returns ``(None, None)`` — the default cap applies
    and the malformed/unpaired override is dropped (matching the deck
    skill's lenient-fallback contract for `.anvil.json`). A bare
    ``max_iterations: 4`` (the default, no rationale — the common memo
    fixture shape) is also dropped: writing the default into the BRIEF
    adds nothing and an unpaired key would be rejected by the strict
    parser.
    """
    mi = anvil_data.get("max_iterations")
    rationale = anvil_data.get("iteration_cap_rationale")
    if not isinstance(mi, int) or isinstance(mi, bool) or mi < 4:
        return None, None
    if not isinstance(rationale, str) or not rationale.strip():
        return None, None
    return mi, rationale.strip()


def _extract_rubric_overrides(anvil_data: dict) -> Optional[dict]:
    """Pull ``rubric_overrides`` from a `.anvil.json` payload.

    Returns the dict verbatim — the BRIEF parser handles validation
    downstream. ``None`` when the key is absent or not a dict.
    """
    ro = anvil_data.get("rubric_overrides")
    if isinstance(ro, dict) and ro:
        return ro
    return None


def _find_cross_thread_refs(
    body_path: Path,
    stems_to_rewrite: Dict[str, str],
) -> List[Tuple[str, str, int]]:
    """Find cross-thread refs in ``body_path`` to rewrite.

    ``stems_to_rewrite`` maps OLD stem → NEW stem. Returns a list of
    ``(old_token, new_token, count)`` tuples for each distinct token found.

    Example: with ``stems_to_rewrite={"memo": "investment-memo"}``, a body
    containing ``"see memo.7 §3"`` returns ``[("memo.7", "investment-memo.7", 1)]``.
    """
    if not body_path.is_file():
        return []
    try:
        text = body_path.read_text(encoding="utf-8")
    except OSError:
        return []
    if not stems_to_rewrite:
        return []
    pattern = _cross_thread_ref_re(list(stems_to_rewrite.keys()))
    counts: Dict[str, Tuple[str, int]] = {}
    for match in pattern.finditer(text):
        old_stem = match.group(1)
        version_n = match.group(2)
        new_stem = stems_to_rewrite[old_stem]
        old_token = f"{old_stem}.{version_n}"
        new_token = f"{new_stem}.{version_n}"
        if old_token == new_token:
            continue
        prior = counts.get(old_token)
        if prior is None:
            counts[old_token] = (new_token, 1)
        else:
            counts[old_token] = (prior[0], prior[1] + 1)
    return [(old, new, count) for old, (new, count) in counts.items()]


def _plan_fully_migrated_doc(
    thread: ThreadInventory,
) -> DocumentPlan:
    """Return a no-op DocumentPlan for an already-migrated thread."""
    return DocumentPlan(
        slug=thread.slug,
        source_dir=thread.parent_dir,
        target_dir=thread.parent_dir,
        notes=[f"{thread.slug}: already migrated; no-op"],
    )


def _plan_post_283_doc(
    inv: ProjectInventory,
    thread: ThreadInventory,
    stems_to_rewrite: Dict[str, str],
) -> DocumentPlan:
    """Build a plan for a thread under POST_283_ANVIL_JSON shape.

    The thread already lives at ``<project>/<slug>/<slug>.N/`` — the
    parent dir is correct. What may need fixing:

    - Body filename is ``memo.md`` → rename to ``<slug>.md``.
    - A ``.anvil.json`` exists → merge into project BRIEF, delete file.
    - Cross-thread refs use old stems → rewrite.
    """
    plan = DocumentPlan(
        slug=thread.slug,
        source_dir=thread.parent_dir,
        target_dir=thread.parent_dir,
    )

    target_body = f"{thread.slug}.md"
    body_renames_planned: List[Path] = []
    for version_dir in thread.version_dirs:
        for body_filename in _SKILL_FIXED_BODY_FILENAMES:
            if body_filename == target_body:
                continue
            src = version_dir / body_filename
            if src.is_file():
                target = version_dir / target_body
                plan.renames.append(Rename(source=src, target=target))
                body_renames_planned.append(target)
                plan.notes.append(
                    f"Rename body: {src.relative_to(inv.project_dir)} → "
                    f"{target.relative_to(inv.project_dir)}"
                )

    # Cross-thread refs in the renamed bodies (and existing <slug>.md bodies).
    for version_dir in thread.version_dirs:
        candidates: List[Path] = []
        # Already-correct body filename — scan in place.
        existing = version_dir / target_body
        if existing.is_file():
            candidates.append(existing)
        # Bodies we're about to rename in — read from source, but the rewrite
        # is recorded against the target path (the apply step renames first).
        for body_filename in _SKILL_FIXED_BODY_FILENAMES:
            if body_filename == target_body:
                continue
            src = version_dir / body_filename
            if src.is_file():
                # Read content from source; record target path for rewrite.
                target = version_dir / target_body
                refs = _find_cross_thread_refs(src, stems_to_rewrite)
                for old, new, count in refs:
                    plan.content_rewrites.append(
                        ContentRewrite(
                            file_path=target,
                            old_string=old,
                            new_string=new,
                            occurrences=count,
                        )
                    )
                continue
        for body in candidates:
            refs = _find_cross_thread_refs(body, stems_to_rewrite)
            for old, new, count in refs:
                plan.content_rewrites.append(
                    ContentRewrite(
                        file_path=body,
                        old_string=old,
                        new_string=new,
                        occurrences=count,
                    )
                )

    # Anvil JSON → BRIEF merge.
    if thread.anvil_json_path is not None:
        data = _read_anvil_json(thread.anvil_json_path)
        target_length, overrides = _extract_target_length(data)
        rubric_overrides = _extract_rubric_overrides(data)
        max_iterations, cap_rationale = _extract_iteration_cap(data)
        plan.brief_merge = BriefMergeOp(
            slug=thread.slug,
            target_length=target_length,
            target_length_overrides=overrides,
            rubric_overrides=rubric_overrides,
            max_iterations=max_iterations,
            iteration_cap_rationale=cap_rationale,
        )
        plan.anvil_json_to_delete = thread.anvil_json_path
        plan.notes.append(
            f"Merge {thread.anvil_json_path.relative_to(inv.project_dir)} into BRIEF; "
            f"delete after merge."
        )
    else:
        # No .anvil.json — still emit a BriefMergeOp so the BRIEF entry exists
        # if the project BRIEF currently lacks it. The actual merge step
        # checks the existing entry to avoid clobbering operator-set fields.
        plan.brief_merge = BriefMergeOp(slug=thread.slug)

    # Nested-but-unmigrated deck/slides/proposal threads carry retained
    # bodies too — apply the same artifact-type inference (#386).
    _apply_retained_body_inference(plan, thread)

    return plan


def _plan_pre_283_doc(
    inv: ProjectInventory,
    thread: ThreadInventory,
    stems_to_rewrite: Dict[str, str],
    artifact_type: Optional[str] = None,
) -> DocumentPlan:
    """Build a plan for a thread whose version dirs sit at the project root.

    Covers both the memo classic shape (no ``<slug>/`` parent at all)
    and the nested-but-flat deck/slides/proposal shape (issue #382 —
    a ``<slug>/`` thread root with BRIEF/refs/assets exists as a
    SIBLING of the flat ``<slug>.N/`` version dirs; the studio canary's
    hand-fix ``2cf3f37`` is the reference shape). Steps:

    1. Create the ``<slug>/`` parent when absent (implicit — happens
       during rename; an existing thread root is kept, its contents
       untouched).
    2. Rename each ``<stem>.N/`` → ``<slug>/<slug>.N/`` (critic
       siblings move alongside).
    3. Rename skill-fixed body files inside (``memo.md`` → ``<slug>.md``).
       Retained body filenames (``deck.md``, ``proposal.tex``) are NOT
       renamed — the slug-echo migration is scoped out for those skills.
    4. Cross-thread refs use old stems → rewrite.
    5. Per-thread ``.anvil.json`` (inside the thread root) or the
       project-root ``.anvil.json`` (if it claims this thread) → merge
       into BRIEF, delete after.
    """
    plan = DocumentPlan(
        slug=thread.slug,
        source_dir=thread.parent_dir,
        target_dir=inv.project_dir / thread.slug,
    )

    target_body = f"{thread.slug}.md"

    # Original version_dir → its post-move target_version_dir (issue
    # #878's foreign-body rename needs this: the directory move is
    # planned first, so any body rename inside it must reference the
    # POST-MOVE path, matching the skill-fixed body-rename pattern below).
    version_dir_targets: Dict[Path, Path] = {}

    # Plan renames for each version dir. The stem may differ from the
    # slug (the canary case is stem="memo", slug=<project-name>); we use
    # the version dir's actual N from its name.
    version_re = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")
    for version_dir in thread.version_dirs:
        m = version_re.match(version_dir.name)
        if m is None:
            continue
        n = m.group("num")
        # Target: <project>/<slug>/<slug>.N/
        target_version_dir = plan.target_dir / f"{thread.slug}.{n}"
        version_dir_targets[version_dir] = target_version_dir
        plan.renames.append(
            Rename(source=version_dir, target=target_version_dir)
        )
        plan.notes.append(
            f"Rename version dir: "
            f"{version_dir.relative_to(inv.project_dir)} → "
            f"{target_version_dir.relative_to(inv.project_dir)}"
        )

        # Inside each renamed version dir, rename the body file.
        for body_filename in _SKILL_FIXED_BODY_FILENAMES:
            if body_filename == target_body:
                continue
            src_body = version_dir / body_filename
            if src_body.is_file():
                # Target paths are AFTER the version-dir rename.
                target_body_path = target_version_dir / target_body
                src_body_at_target = target_version_dir / body_filename
                plan.renames.append(
                    Rename(
                        source=src_body_at_target,
                        target=target_body_path,
                    )
                )
                plan.notes.append(
                    f"Rename body: "
                    f"{src_body.relative_to(inv.project_dir)} → "
                    f"{target_body_path.relative_to(inv.project_dir)}"
                )
                # Cross-thread refs scanned from current source path; the
                # rewrite is recorded against the FINAL target body path.
                refs = _find_cross_thread_refs(src_body, stems_to_rewrite)
                for old, new, count in refs:
                    plan.content_rewrites.append(
                        ContentRewrite(
                            file_path=target_body_path,
                            old_string=old,
                            new_string=new,
                            occurrences=count,
                        )
                    )
        # Also consider critic sibling dirs (<stem>.N.review/, etc.) for
        # rename. We rename them so the discovery walk continues to work.
        for sibling in _iter_critic_siblings(version_dir):
            sibling_name = sibling.name
            # Replace the <stem>.N prefix with <slug>.N.
            prefix = f"{m.group('stem')}.{n}"
            if sibling_name.startswith(f"{prefix}."):
                new_name = f"{thread.slug}.{n}." + sibling_name[len(prefix) + 1:]
                target_sibling = plan.target_dir / new_name
                plan.renames.append(
                    Rename(source=sibling, target=target_sibling)
                )
                plan.notes.append(
                    f"Rename critic sibling: "
                    f"{sibling.relative_to(inv.project_dir)} → "
                    f"{target_sibling.relative_to(inv.project_dir)}"
                )

    # Anvil JSON merge. Two carriers, in precedence order:
    #
    # 1. A per-thread .anvil.json inside the sibling thread root
    #    (<project>/<slug>/.anvil.json — the deck-skill carrier on
    #    nested-but-flat threads, issue #382). Recorded by the detector
    #    as ``thread.anvil_json_path``.
    # 2. The project-root .anvil.json (the memo classic one-per-project
    #    location); claim it for this thread when no other thread has.
    claimed_anvil: Optional[Path] = None
    if thread.anvil_json_path is not None:
        claimed_anvil = thread.anvil_json_path
    else:
        root_anvil = inv.project_dir / ANVIL_JSON_FILENAME
        if root_anvil.is_file() and root_anvil in inv.extra_anvil_jsons:
            claimed_anvil = root_anvil

    if claimed_anvil is not None:
        data = _read_anvil_json(claimed_anvil)
        target_length, overrides = _extract_target_length(data)
        rubric_overrides = _extract_rubric_overrides(data)
        max_iterations, cap_rationale = _extract_iteration_cap(data)
        plan.brief_merge = BriefMergeOp(
            slug=thread.slug,
            target_length=target_length,
            target_length_overrides=overrides,
            rubric_overrides=rubric_overrides,
            max_iterations=max_iterations,
            iteration_cap_rationale=cap_rationale,
        )
        plan.anvil_json_to_delete = claimed_anvil
        plan.notes.append(
            f"Merge {claimed_anvil.relative_to(inv.project_dir)} into BRIEF; "
            f"delete after merge."
        )
        if data.get("max_iterations") is not None and max_iterations is None:
            plan.notes.append(
                f"{thread.slug}: max_iterations override NOT carried into "
                f"BRIEF (default cap, missing/empty rationale, or below "
                f"the >=4 floor); the default applies."
            )
    else:
        plan.brief_merge = BriefMergeOp(slug=thread.slug)

    # Surface the retained-body decision for non-memo threads so the
    # operator sees (a) why no body rename was planned and (b) which
    # artifact_type the BRIEF entry was inferred to carry (issue #386).
    # Keys off the dedicated retained-body inventory surface so it fires
    # for `.tex`-bodied proposal threads too (the pre-#386 silent-default
    # gap: `body_filenames` is `*.md`-only, so proposal threads got the
    # 'investment-memo' default with no note at all).
    _apply_retained_body_inference(plan, thread)

    # Bare threads (issue #408): no anvil config anywhere means the
    # BRIEF entry is SYNTHESIZED, so the silent 'investment-memo'
    # default above becomes an inferred-with-note value paired with an
    # operator-confirmation TODO marker.
    if inv.is_bare:
        _apply_bare_inference(
            plan,
            thread,
            stems_to_rewrite,
            artifact_type=artifact_type,
            version_dir_targets=version_dir_targets,
        )

    return plan


def _apply_retained_body_inference(
    plan: DocumentPlan, thread: ThreadInventory
) -> None:
    """Infer the BRIEF artifact_type from a retained body filename (#386).

    When the thread's inventory observed a retained body
    (``deck.md`` / ``proposal.tex``), set the inferred skill-identity
    artifact_type on the plan's :class:`BriefMergeOp` and surface an
    operator-facing note. ``deck.md`` infers ``deck`` with an explicit
    slides-ambiguity caveat (``anvil:slides`` threads also use
    ``deck.md`` — body shape alone cannot distinguish them). No retained
    body → no-op (memo-shaped threads keep the 'investment-memo'
    default with no note, as before).
    """
    retained = sorted(set(thread.retained_body_filenames))
    if not retained:
        return

    inferred_types = sorted(
        {
            _RETAINED_BODY_ARTIFACT_TYPES[b]
            for b in retained
            if b in _RETAINED_BODY_ARTIFACT_TYPES
        }
    )
    note = (
        f"{thread.slug}: body filename {', '.join(retained)} retained "
        f"(slug-echo rename is scoped out for deck/slides/proposal per "
        f"issue #382)"
    )
    if len(inferred_types) == 1:
        inferred = inferred_types[0]
        if plan.brief_merge is not None:
            plan.brief_merge.artifact_type = inferred
        note += (
            f"; artifact_type inferred as '{inferred}' from "
            f"{', '.join(retained)}"
        )
        if inferred == "deck":
            note += (
                " (note: anvil:slides threads also use deck.md — edit "
                "the BRIEF entry to 'slides' for a talk deck)"
            )
        note += " — edit the BRIEF entry if wrong."
    else:
        # Conflicting retained bodies across version dirs — cannot infer
        # a single type; keep the default and say so.
        note += (
            f"; conflicting retained bodies prevent artifact_type "
            f"inference — BRIEF entry defaults to "
            f"'{BriefMergeOp.artifact_type}'; edit after migration."
        )
    plan.notes.append(note)


def _read_text_lenient(path: Path) -> str:
    """Read ``path`` as UTF-8 text; return ``""`` on any failure."""
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _infer_tex_artifact_type(text: str) -> Optional[str]:
    """Infer a skill-identity artifact_type from LaTeX body content.

    Inference table (issue #408, curator-resolved):

    - ``\\documentclass{anvil-proposal}`` (or any anvil-proposal.cls
      reference) → ``proposal``
    - any other ``\\documentclass`` → ``paper`` (registered as a
      skill-identity value under #408 as ``pub``; the skill was renamed
      ``pub`` → ``paper`` under #694 and BRIEF synthesis now emits the
      canonical ``paper``)
    - no ``\\documentclass`` → ``None`` (caller keeps the memo-class
      default, still TODO-marked)
    """
    if "anvil-proposal" in text:
        return "proposal"
    if "\\documentclass" in text:
        return "paper"
    return None


def _apply_native_provisional_inference(
    plan: DocumentPlan,
    thread: ThreadInventory,
    observed: List[str],
) -> None:
    """Record a native ip-uspto-provisional thread (issue #503).

    Called by :func:`_apply_bare_inference` when ``provisional.tex`` is
    among the observed bodies. The recognition is FILENAME-driven, not
    content-driven — no ``\\documentclass`` scan runs here (SKILL.md:160:
    no provisional-vs-full inference). Like every bare inference the
    value is TODO-marked (``inferred=True``) and surfaced as a plan note
    plus an ``operator_todos`` checklist row — never a silent default.

    Body handling mirrors the #382/#408 recorded-but-never-renamed
    carve-out: ``provisional.tex`` is the body, recorded with a deferral
    note (anvil's canonical body is ``spec.tex``, but renaming a
    consumer's externally-compiled ``provisional.tex`` would break their
    xelatex/build tooling). When ``counsel_memo.tex`` is also present it
    is recorded as a PRESERVED COMPANION — never selected as the body,
    never renamed.
    """
    if plan.brief_merge is None:
        return

    plan.brief_merge.artifact_type = "ip-uspto-provisional"
    plan.brief_merge.inferred = True
    plan.brief_merge.todo_comment = (
        f"TODO(operator): confirm — recognized from "
        f"{PROVISIONAL_BODY_FILENAME} body filename"
    )
    plan.notes.append(
        f"{plan.slug}: artifact_type recognized as 'ip-uspto-provisional' "
        f"from the {PROVISIONAL_BODY_FILENAME} body filename (FILENAME "
        f"signal, not \\documentclass — anvil's provisional and full "
        f"ip-uspto specs share \\documentclass{{anvil-uspto}}, so content "
        f"cannot disambiguate them) — confirm in BRIEF (TODO marker "
        f"emitted)."
    )
    plan.operator_todos.append(
        f"`{plan.slug}`: confirm `artifact_type: ip-uspto-provisional` "
        f"(recognized from {PROVISIONAL_BODY_FILENAME})."
    )

    # Body filename: recorded + deferred, never renamed (#382/#408
    # carve-out — anvil's canonical body is `spec.tex`, but the
    # consumer's `provisional.tex` is externally compiled).
    plan.notes.append(
        f"{plan.slug}: body filename {PROVISIONAL_BODY_FILENAME} recorded "
        f"but NOT renamed (anvil's canonical provisional body is "
        f"`spec.tex`; renaming a consumer's externally-compiled "
        f"{PROVISIONAL_BODY_FILENAME} would break their xelatex/build "
        f"tooling). Rename to `spec.tex` manually if desired."
    )
    plan.operator_todos.append(
        f"`{plan.slug}`: body filename `{PROVISIONAL_BODY_FILENAME}` "
        f"retained inside version dirs — rename to `spec.tex` manually "
        f"only if no external tooling consumes the fixed name."
    )

    # Counsel-memo companion: recognized, recorded, never the body,
    # never renamed.
    if has_counsel_memo_companion(observed):
        plan.notes.append(
            f"{plan.slug}: {COUNSEL_MEMO_FILENAME} recognized as a "
            f"PRESERVED COMPANION (a finalize-output counsel memo, never "
            f"a version-dir body) — recorded and left in place, never "
            f"selected as the body and never renamed."
        )
        plan.operator_todos.append(
            f"`{plan.slug}`: {COUNSEL_MEMO_FILENAME} preserved as a "
            f"companion alongside {PROVISIONAL_BODY_FILENAME} (not the "
            f"body)."
        )


def _foreign_md_body_candidates(thread: ThreadInventory) -> List[str]:
    """Return the sorted non-anvil ``.md`` body filenames on ``thread`` (#878).

    A bare thread (no anvil config anywhere) may carry a body filename
    fixed by a FOREIGN pipeline (e.g. a hand-rolled blog tool's
    ``post.md``) rather than any historical anvil skill name.
    ``_SKILL_FIXED_BODY_FILENAMES`` only recognizes anvil's OWN historical
    fixed names (``memo.md``, ``proposal.md``, ...) — a foreign name
    matches none of them, so the skill-fixed rename loop in
    :func:`_plan_pre_283_doc` has nothing to match (issue #878's root
    cause: the correct declaration, ``artifact_type: essay``, would come
    from the very BRIEF this run synthesizes).

    Scans the thread's aggregated ``body_filenames`` (every ``*.md``
    observed across its version dirs) for candidates that are neither the
    canonical ``<slug>.md`` target nor a name anvil itself recognizes
    (skill-fixed or retained). The caller decides what to do with the
    result: exactly one candidate is an unambiguous foreign body (renamed
    by :func:`_apply_foreign_md_body_rename`); more than one is ambiguous
    and left for the operator to resolve by hand rather than guessed
    (issue #878's suggested acceptance criteria, option 2 — "detection of
    a single consistent non-anvil body filename across a bare project").
    """
    target_body = f"{thread.slug}.md"
    excluded = set(_SKILL_FIXED_BODY_FILENAMES) | set(_RETAINED_BODY_FILENAMES)
    excluded.add(target_body)
    # Defensive only: ``changelog.md`` is already filtered out upstream by
    # ``_observed_body_filenames`` (anvil/lib/project_detect.py), so it never
    # reaches ``ThreadInventory.body_filenames``. Kept so this predicate stays
    # correct on its own terms if that upstream filter ever moves.
    excluded.add("changelog.md")
    return sorted({b for b in thread.body_filenames if b not in excluded})


def _detect_foreign_md_body_filename(thread: ThreadInventory) -> Optional[str]:
    """Return the sole foreign ``.md`` body filename on ``thread``, or ``None``.

    Thin single-candidate wrapper over :func:`_foreign_md_body_candidates`
    — ``None`` when there is no candidate (already canonical) OR when
    there are multiple distinct candidates (ambiguous; see
    :func:`_apply_bare_inference` for the ambiguity-note path).
    """
    candidates = _foreign_md_body_candidates(thread)
    if len(candidates) != 1:
        return None
    return candidates[0]


def _apply_foreign_md_body_rename(
    plan: DocumentPlan,
    thread: ThreadInventory,
    foreign_name: str,
    stems_to_rewrite: Dict[str, str],
    version_dir_targets: Optional[Dict[Path, Path]] = None,
) -> None:
    """Plan the rename of a bare thread's foreign ``.md`` body (issue #878).

    Renames every version dir's ``foreign_name`` to the canonical
    ``<slug>.md`` — the same slug-echo target every other markdown-bodied
    artifact-class skill converges on. Unlike the historical
    ``_SKILL_FIXED_BODY_FILENAMES`` loop (which only recognizes anvil's
    OWN prior fixed names), this fires for a name anvil has never seen
    before, because on a bare thread it is — by construction (the
    single-candidate constraint in
    :func:`_detect_foreign_md_body_filename`) — the only body candidate
    present. Cross-thread references inside the renamed body are rewritten
    the same way the skill-fixed rename loop does. Paired with a
    ``# TODO(operator)`` confirmation note (never a silent rename),
    mirroring the #408 bare-inference discipline.

    ``version_dir_targets`` maps each ORIGINAL ``version_dir`` to its
    POST-MOVE path (the pre-#283 classic thread's directory-nesting move,
    planned earlier in ``plan.renames``). The apply step trusts rename
    order (:class:`Rename`'s dependency-order contract), so this
    ``Rename`` entry must reference the post-move path — mirroring the
    skill-fixed body-rename pattern in :func:`_plan_pre_283_doc`. The
    on-disk existence checks and cross-thread-ref scan still read from
    the ORIGINAL (current, pre-move) path.
    """
    target_body = f"{thread.slug}.md"
    version_dir_targets = version_dir_targets or {}
    renamed_any = False
    for version_dir in thread.version_dirs:
        src_on_disk = version_dir / foreign_name
        existing_target_on_disk = version_dir / target_body
        if not src_on_disk.is_file() or existing_target_on_disk.is_file():
            continue
        post_move_dir = version_dir_targets.get(version_dir, version_dir)
        src = post_move_dir / foreign_name
        target = post_move_dir / target_body
        plan.renames.append(Rename(source=src, target=target))
        renamed_any = True
        refs = _find_cross_thread_refs(src_on_disk, stems_to_rewrite)
        for old, new, count in refs:
            plan.content_rewrites.append(
                ContentRewrite(
                    file_path=target,
                    old_string=old,
                    new_string=new,
                    occurrences=count,
                )
            )
    if not renamed_any:
        return
    plan.notes.append(
        f"{plan.slug}: body filename {foreign_name} recognized as the "
        f"sole foreign (non-anvil) body candidate on this bare thread — "
        f"renamed to {target_body}. TODO(operator): confirm the rename is "
        f"correct (e.g. matches the foreign pipeline's fixed output name) "
        f"before applying."
    )
    plan.operator_todos.append(
        f"`{plan.slug}`: confirm the rename `{foreign_name}` -> "
        f"`{target_body}` (recognized as the sole foreign body candidate)."
    )


def _apply_bare_inference(
    plan: DocumentPlan,
    thread: ThreadInventory,
    stems_to_rewrite: Optional[Dict[str, str]] = None,
    artifact_type: Optional[str] = None,
    version_dir_targets: Optional[Dict[Path, Path]] = None,
) -> None:
    """Infer the BRIEF artifact_type for a BARE thread (issue #408).

    Bare threads carry no anvil config, so every BRIEF value is a
    synthesis-time proposal: the inference is recorded on the
    :class:`BriefMergeOp` with ``inferred=True`` plus a ``todo_comment``
    operator-confirmation marker, mirrored into ``plan.operator_todos``
    (the body-prose checklist that survives BRIEF rewrites), and
    surfaced as a plan note — never a silent default.

    Inference inputs, in precedence order:

    1. Native ``provisional.tex`` / ``counsel_memo.tex`` recognition
       (issue #503) — unconditional; a native provisional filename is a
       stronger, legal-stakes signal than any operator flag.
    2. A foreign (non-anvil) ``.md`` body filename (issue #878) — renamed
       to ``<slug>.md`` via :func:`_detect_foreign_md_body_filename` /
       :func:`_apply_foreign_md_body_rename` regardless of whether
       ``artifact_type`` resolves the type declaration below (the rename
       is about WHICH FILE is the body, not what skill it belongs to).
    3. An explicit ``artifact_type`` (``--artifact-type``, issue #878):
       when given, it is the operator's declaration — set directly with
       no TODO marker, short-circuiting the content-inference heuristics
       below (this is what closes the circularity: the BRIEF this run
       synthesizes can now carry the correct declared type instead of the
       silent ``investment-memo`` default).
    4. ``thread.observed_body_files`` (non-``.md`` candidate bodies,
       ``*.tex``): read the newest version's observed body and apply
       :func:`_infer_tex_artifact_type`. The observed body filename is
       recorded-but-never-renamed (the #382 slug-echo carve-out:
       root-level build artifacts are direct evidence that external
       tooling consumes the fixed name) with a deferral note.
    5. Markdown bodies (non-skill-fixed — skill-fixed bodies preclude
       bareness): keep the memo-class ``investment-memo`` default,
       TODO-marked.
    """
    if plan.brief_merge is None:
        return

    observed = sorted(set(thread.observed_body_files))

    # Filename-first recognition of a native ip-uspto-provisional thread
    # (issue #503). ``provisional.tex`` is a SAFE explicit signal:
    # anvil's own provisional body is ``spec.tex`` with
    # ``\documentclass{anvil-uspto}`` — the SAME class the full ip-uspto
    # spec uses — so the ``\documentclass`` scan below cannot disambiguate
    # a provisional from a full application (SKILL.md:160 forbids that
    # inference). The operator's body FILENAME is the declaration, so we
    # short-circuit content inference when it is present.
    if has_native_provisional_body(observed):
        _apply_native_provisional_inference(plan, thread, observed)
        return

    # Counsel-memo-only refusal (issue #503): a version dir carrying
    # ``counsel_memo.tex`` but NO ``provisional.tex`` is not a fileable
    # body — a counsel memo is a finalize-OUTPUT companion. Refuse before
    # any mutation (planning is pure; nothing is touched).
    if has_counsel_memo_companion(observed):
        raise PlanError(
            f"Thread `{thread.slug}` carries `{COUNSEL_MEMO_FILENAME}` "
            f"but no `{PROVISIONAL_BODY_FILENAME}`. A counsel memo is a "
            f"finalize-output companion (anvil writes it into "
            f"`<thread>.counsel/`), not a fileable provisional body. "
            f"Suggested fix: add the `{PROVISIONAL_BODY_FILENAME}` body "
            f"this counsel memo accompanies, then re-run. Nothing was "
            f"modified."
        )

    # Foreign (non-anvil) markdown body detection (issue #878) — applies
    # regardless of whether --artifact-type is given below.
    foreign_candidates = _foreign_md_body_candidates(thread)
    if len(foreign_candidates) == 1:
        _apply_foreign_md_body_rename(
            plan,
            thread,
            foreign_candidates[0],
            stems_to_rewrite or {},
            version_dir_targets=version_dir_targets,
        )
    elif len(foreign_candidates) > 1:
        plan.notes.append(
            f"{thread.slug}: multiple distinct non-canonical .md body "
            f"filenames observed ({', '.join(foreign_candidates)}) — "
            f"ambiguous, so NO body rename was planned. Resolve manually "
            f"(rename the correct one to {thread.slug}.md) before or "
            f"after applying."
        )
        plan.operator_todos.append(
            f"`{thread.slug}`: multiple non-canonical body filenames "
            f"observed ({', '.join(foreign_candidates)}) — rename the "
            f"correct one to `{thread.slug}.md` manually."
        )

    # Explicit --artifact-type (issue #878): the operator's declaration
    # takes precedence over content inference and needs no TODO marker.
    if artifact_type is not None:
        plan.brief_merge.artifact_type = artifact_type
        plan.brief_merge.inferred = False
        plan.brief_merge.todo_comment = None
        plan.notes.append(
            f"{thread.slug}: artifact_type set to '{artifact_type}' "
            f"(--artifact-type flag — declared, not inferred)."
        )
        return

    if observed:
        # Read the newest version dir's observed body for content
        # heuristics (the latest version is the best evidence of what
        # the thread currently is).
        sample_name: Optional[str] = None
        sample_text = ""
        for version_dir in reversed(thread.version_dirs):
            for name in observed:
                candidate = version_dir / name
                if candidate.is_file():
                    sample_name = name
                    sample_text = _read_text_lenient(candidate)
                    break
            if sample_name is not None:
                break
        if sample_name is None:
            sample_name = observed[0]

        inferred = _infer_tex_artifact_type(sample_text)
        if inferred is not None:
            plan.brief_merge.artifact_type = inferred
            plan.brief_merge.inferred = True
            plan.brief_merge.todo_comment = (
                f"TODO(operator): confirm — inferred from {sample_name} "
                f"\\documentclass"
            )
            plan.notes.append(
                f"{plan.slug}: artifact_type inferred as '{inferred}' from "
                f"{sample_name} (\\documentclass scan; bare thread, no anvil "
                f"config to merge from) — confirm in BRIEF (TODO marker "
                f"emitted)."
            )
            plan.operator_todos.append(
                f"`{plan.slug}`: confirm `artifact_type: {inferred}` "
                f"(inferred from {sample_name})."
            )
        else:
            plan.brief_merge.inferred = True
            plan.brief_merge.todo_comment = (
                f"TODO(operator): confirm — could not infer from "
                f"{sample_name}; defaulted"
            )
            plan.notes.append(
                f"{plan.slug}: artifact_type could not be inferred from "
                f"{sample_name} (no \\documentclass found); defaulting to "
                f"'{plan.brief_merge.artifact_type}' with a TODO marker — "
                f"edit the BRIEF entry."
            )
            plan.operator_todos.append(
                f"`{plan.slug}`: confirm `artifact_type: "
                f"{plan.brief_merge.artifact_type}` (could not infer from "
                f"{sample_name})."
            )

        # Body filename: record + defer, never rename (#382 carve-out).
        observed_list = ", ".join(observed)
        plan.notes.append(
            f"{plan.slug}: body filename {observed_list} recorded but NOT "
            f"renamed (slug-echo carve-out per issue #382 — external "
            f"tooling such as latexmk/Makefile may consume the fixed "
            f"name); rename manually if desired."
        )
        plan.operator_todos.append(
            f"`{plan.slug}`: body filename `{observed_list}` retained "
            f"inside version dirs — rename manually only if no external "
            f"tooling consumes the fixed name."
        )
        return

    # No observed candidate bodies: a markdown-bodied (or empty) bare
    # thread keeps the memo-class default, TODO-marked.
    plan.brief_merge.inferred = True
    plan.brief_merge.todo_comment = (
        "TODO(operator): confirm — memo-class default for a bare thread"
    )
    plan.notes.append(
        f"{plan.slug}: artifact_type defaulted to "
        f"'{plan.brief_merge.artifact_type}' (bare thread with markdown "
        f"body; no anvil config to merge from) — confirm in BRIEF (TODO "
        f"marker emitted)."
    )
    plan.operator_todos.append(
        f"`{plan.slug}`: confirm `artifact_type: "
        f"{plan.brief_merge.artifact_type}` (memo-class default)."
    )


def _iter_critic_siblings(version_dir: Path) -> List[Path]:
    """Return list of critic sibling dirs for ``version_dir``.

    A critic sibling has the shape ``<stem>.<N>.<critic>/`` where the
    ``<stem>.<N>`` prefix matches the version dir's basename.
    """
    parent = version_dir.parent
    out: List[Path] = []
    if not parent.is_dir():
        return out
    prefix = version_dir.name + "."
    try:
        for child in parent.iterdir():
            if not child.is_dir():
                continue
            if child.name == version_dir.name:
                continue
            if child.name.startswith(prefix):
                out.append(child)
    except OSError:
        return out
    return out


def build_plan(
    project_dir: Path,
    shape: Optional[Shape] = None,
    inventory: Optional[ProjectInventory] = None,
    artifact_type: Optional[str] = None,
) -> Plan:
    """Build a :class:`Plan` for ``project_dir``.

    Parameters
    ----------
    project_dir
        Project root.
    shape
        Pre-computed shape; computed via :func:`detect_shape` when omitted.
    inventory
        Pre-computed inventory; computed via :func:`inventory_project`
        when omitted.
    artifact_type
        Optional ``--artifact-type`` (issue #878), validated against the
        two-tier #394 registry (:func:`_validate_migrate_artifact_type`).
        Applied to every synthesized ``documents:`` entry on a BARE
        thread (:data:`ProjectInventory.is_bare`) — the operator's
        explicit declaration, replacing the inferred/defaulted value with
        no TODO marker. Closes the bare-synthesis circularity: without
        it, a thread's correct declaration (e.g. ``artifact_type:
        essay``) would come from the very BRIEF this run synthesizes.
        Ignored (has no effect) on non-bare threads, which already carry
        or merge a declared/legacy type. ``None`` (the default) preserves
        prior behavior byte-for-byte.

    Returns
    -------
    A :class:`Plan` carrying per-document plans. When the project is
    :data:`Shape.FULLY_MIGRATED`, the plan's ``documents`` list contains
    a no-op entry per thread (the apply step then becomes zero-diff).

    Raises
    ------
    PlanError
        When ``artifact_type`` is given but is neither a registered nor a
        consumer-declared artifact type. Raised BEFORE any planning or
        mutation.
    """
    project_dir = Path(project_dir).resolve()
    if inventory is None:
        inventory = inventory_project(project_dir)
    if shape is None:
        from .detect import _classify
        shape = _classify(inventory)

    if artifact_type is not None:
        artifact_type = _validate_migrate_artifact_type(
            artifact_type, project_dir
        )

    plan = Plan(project_dir=project_dir, shape=shape)
    # Bare sub-state (issue #408): synthesize the BRIEF automatically —
    # there is no legacy config to merge from, so synthesis-with-TODO
    # markers is the only sane behavior (dry-run-by-default is the
    # operator's safety surface; no extra flag).
    plan.synthesize_brief = inventory.is_bare

    # Build the stem rewrite map. Used for cross-thread reference rewriting.
    stems_to_rewrite: Dict[str, str] = {}
    for thread in inventory.threads:
        version_re = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")
        for version_dir in thread.version_dirs:
            m = version_re.match(version_dir.name)
            if m is None:
                continue
            stem = m.group("stem")
            if stem != thread.slug:
                stems_to_rewrite[stem] = thread.slug

    # Record existing BRIEF slugs so the planner doesn't drop them on a
    # partial migration.
    if inventory.has_project_brief:
        from .detect import _project_brief_slugs
        plan.preexisting_brief_slugs = _project_brief_slugs(project_dir)

    if shape == Shape.FULLY_MIGRATED:
        for thread in inventory.threads:
            plan.documents.append(_plan_fully_migrated_doc(thread))
        return plan

    if shape == Shape.POST_283_ANVIL_JSON:
        for thread in inventory.threads:
            # Mixed-grammar projects (issue #382): a project BRIEF may
            # exist (e.g., memo threads already migrated) while a
            # deck/slides/proposal thread still sits flat at the project
            # root. Flat threads need the nesting move, not the
            # in-place post-#283 cleanup — dispatch per thread.
            if thread.parent_dir == inventory.project_dir:
                plan.documents.append(
                    _plan_pre_283_doc(
                        inventory, thread, stems_to_rewrite,
                        artifact_type=artifact_type,
                    )
                )
            else:
                plan.documents.append(
                    _plan_post_283_doc(inventory, thread, stems_to_rewrite)
                )
        # Also delete any extra .anvil.json files (excluding any already
        # claimed by a flat-thread doc plan above).
        already_claimed = {
            doc.anvil_json_to_delete for doc in plan.documents
            if doc.anvil_json_to_delete is not None
        }
        for extra in inventory.extra_anvil_jsons:
            if extra not in already_claimed:
                plan.extra_anvil_jsons_to_delete.append(extra)
        return plan

    if shape == Shape.PRE_283_CLASSIC:
        for thread in inventory.threads:
            plan.documents.append(
                _plan_pre_283_doc(
                    inventory, thread, stems_to_rewrite,
                    artifact_type=artifact_type,
                )
            )
        # Pre-#283 had a project-root .anvil.json which gets claimed by
        # the per-doc plan above (the first thread's plan); any remaining
        # extras still get cleaned up here.
        already_claimed = {
            doc.anvil_json_to_delete for doc in plan.documents
            if doc.anvil_json_to_delete is not None
        }
        for extra in inventory.extra_anvil_jsons:
            if extra not in already_claimed:
                plan.extra_anvil_jsons_to_delete.append(extra)
        return plan

    # Shape.UNKNOWN — return an empty plan; caller dispatches the error.
    return plan


__all__ = [
    "BriefMergeOp",
    "ContentRewrite",
    "DocumentPlan",
    "Plan",
    "PlanError",
    "Rename",
    "build_plan",
]
