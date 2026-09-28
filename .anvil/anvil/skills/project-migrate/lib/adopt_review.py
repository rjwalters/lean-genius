"""Single-file ``review.md`` → critic-sibling content conversion (issue #454).

Phase 3a of the issue #432 foreign-grammar adoption arc (Phase 1 =
``--adopt-vn``, PR #439; Phase 2 = ``--adopt-family``, issue #440). Phases
1 and 2 make foreign version-dir and critic-sibling **names** canonical;
this phase is the deferred **content** step: converting a foreign critic
sibling's single-file prose ``review.md`` into a payload
``anvil/lib/critics.py::discover_critics`` can recognize.

Honest scope: STUB conversion, NOT prose→score extraction
---------------------------------------------------------

The binding curation decision (issue #454, 2026-06-12): foreign
single-file ``review.md`` payloads (sphere ``.enablement`` / ``.s101`` /
``.fto`` / ``.critic`` / ``.audit2`` / ``.pre_flight`` siblings) were
**never scored on any anvil rubric**. There is no per-dimension table, no
``Total: X/Y``, no ``advance: true|false`` to parse. Synthesizing /44
scores from foreign prose would be **fabrication**, and a deterministic
pass cannot do it honestly. An LLM rescoring pass is exactly
``rubric-rebackport --rescore``'s territory, which is explicitly scoped
out (it targets *anvil-shaped* legacy reviews — its heuristics key on a
known ``rubric_total`` foreign reviews lack).

So this mode does the minimal honest thing: for each sidecar dir holding
ONLY ``review.md`` (failing ``critics._has_recognizable_review``), write a
canonical ``_review.json`` that is **recognizable-but-explicitly-unscored**
(empty ``scores``/``findings``/``critical_flags``; null
``total``/``threshold``/``verdict``; ``unscored: True``) plus a sibling
``_meta.json`` foreign-provenance marker, while preserving the original
``review.md`` **byte-identical**. NO LLM call. NO score synthesis.

Phase 3b: operator-driven LLM rescore (issue #507)
--------------------------------------------------

Phase 3b turns a Phase-3a stub into a **real scored review**. It is an
opt-in ``--rescore`` modifier on ``--adopt-review`` — NOT a
``rubric-rebackport`` extension (rubric-rebackport's detector only sees
``.review`` siblings and its ``--rescore`` requires a prior anvil score a
stub lacks; see the issue #507 curation comment for the three
code-grounded reasons).

The scoring itself is an **operator-driven LLM step that stays in the
slash-command runtime** — the exact precedent set by
``anvil/skills/rubric-rebackport/lib/rescore.py`` ("the actual LLM call
belongs in the consumer's slash-command runtime, not in this Python
library"). The Python here is a THIN **planner + marker-flip +
atomic-write** harness:

- :func:`build_rescore_plan` scans an adopted tree for sidecars carrying a
  Phase-3a stub (``_review.json`` ``unscored: true`` + ``_meta.json``
  ``source: foreign-adopted``), resolves the target anvil rubric per
  sidecar (BRIEF ``documents:`` block → body-filename fallback), and
  returns a (possibly empty) plan. A stub whose rubric cannot be resolved
  is SKIPPED with an operator-visible note — never guessed (the honesty
  guard, mirroring rubric-rebackport's ``inferred_skill is None`` → skip).
- The operator/LLM reads the verbatim ``review.md`` + the resolved rubric
  and produces per-dimension scores. The caller hands those back as a
  :class:`ScoredReviewInput`.
- :func:`apply_rescore_plan` writes the scored :class:`Review` back
  per-sidecar atomically — reusing Phase 3a's ``_convert_one``
  staged/backup/swap pattern so ``review.md`` stays byte-identical — flips
  ``unscored`` ``True → False``, stamps the v0.4.0 per-review rubric
  fields (``rubric_id`` / ``rubric_total`` / ``advance_threshold``) into
  ``_meta.json``, and records the lineage (``rescored_from:
  foreign-adopted``, retaining ``origin_filename``).

Design notes
------------

- **Pure planner — no mutations.** :func:`build_adopt_review_plan` reads
  the tree but never writes. The dry-run-by-default contract (the
  universal invariant in this skill) depends on it. Mutations live in
  :func:`apply_adopt_review_plan`, gated behind ``--apply``.
- **Standalone on adopted trees (single responsibility).** This mode does
  NOT chain after ``--adopt-family``; it runs on a tree whose names are
  already canonical (``<slug>/<slug>.{N}/`` with ``<slug>.{N}.<tag>``
  siblings). Composition is via two operator runs. It touches NO
  ``BRIEF.md`` — it is purely a critic-sibling content conversion.
- **Verbatim preservation.** ``review.md`` is copied into the staging dir
  byte-for-byte; the stub is purely additive (``_review.json`` +
  ``_meta.json`` written *beside* it). The original is never mutated.
- **Atomic, crash-safe writes via** :mod:`anvil.lib.sidecar`. Each
  conversion stages a full replacement of the sidecar dir
  (``review.md`` copy + the two new files) into a leading-dot ``.tmp``
  staging dir, then swaps it into place atomically — the existing dir is
  moved aside first (``staged_sidecar`` refuses a pre-existing target),
  the staging dir renamed in, and the moved-aside dir removed. On any
  mid-write failure the original dir is restored untouched.
- **Idempotence.** A sidecar that already carries ``_review.json``
  (a prior conversion, or a real review) passes
  ``_has_recognizable_review`` and is skipped — re-running yields an
  empty (no-op) plan.

Public API
----------

- ``AdoptReviewError`` — typed plan-time / apply-time refusal.
- ``StubConversion`` — one planned sidecar conversion.
- ``AdoptReviewPlan`` — the (possibly empty) batch of conversions.
- ``build_adopt_review_plan(directory)`` — pure planner.
- ``apply_adopt_review_plan(plan)`` — execute (``--apply`` only).
"""

from __future__ import annotations

import json
import shutil
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional

from anvil.lib.critics import (
    CANONICAL_REVIEW_FILENAME,
    _has_recognizable_review,
    _infer_critic_id,
    _infer_version_dir,
)
from anvil.lib.review_schema import Kind, Review, Score, Verdict
from anvil.lib.sidecar import cleanup_one_staging, staged_sidecar

from .detect import _VERSION_DIR_RE
from .rescore_rubrics import (
    RubricIdentity,
    _build_brief_skill_map,
    resolve_rubric_for_sidecar,
)


class AdoptReviewError(ValueError):
    """Plan-time or apply-time conversion refusal."""


# The single-file payload filename the foreign critic siblings carry. This
# is the ONLY recognized prose payload for stub conversion — a sidecar
# holding a differently-named prose file is left untouched (reported as a
# skip) rather than guessed at.
FOREIGN_REVIEW_FILENAME = "review.md"

# The foreign-provenance sidecar marker filename. Distinct from the
# legacy ip-uspto ``_meta.json`` triple member: this marker is paired with
# a canonical ``_review.json`` (the unscored stub), so it never triggers
# the legacy ip-uspto adapter (which requires ``_summary.md`` +
# ``findings.md`` + ``_meta.json`` ALL present and NO ``_review.json``).
PROVENANCE_FILENAME = "_meta.json"

# The provenance-marker contract (issue #454 curation comment). Stamped
# verbatim onto every converted sidecar's ``_meta.json`` so a downstream
# reader can distinguish an unscored-foreign stub from a real review.
PROVENANCE_SOURCE = "foreign-adopted"
PROVENANCE_ADOPTED_BY = "anvil:project-migrate#454"


# A ``<slug>.<N>.<tag>`` critic sidecar under an adopted tree. The version
# stem ``<slug>.<N>`` must itself end in ``.<digits>`` (the canonical
# version-dir grammar) and the tag is a single dot-free segment (the
# ``discover_critics`` single-segment tag rule).
def _split_sidecar_name(name: str) -> Optional[tuple]:
    """Return ``(version_dir_name, tag)`` for a ``<slug>.<N>.<tag>`` dir.

    Returns ``None`` when ``name`` is not a critic-sibling shape: the
    trailing tag must be a single dot-free segment AND the remaining stem
    must be a canonical ``<slug>.<N>`` version dir (ending in
    ``.<digits>``). This is the same shape ``discover_critics`` enumerates
    — we mirror it so the planner only converts dirs discovery WOULD see
    once a ``_review.json`` lands.
    """
    head, sep, tag = name.rpartition(".")
    if not sep or not head or not tag:
        return None
    if "." not in head:
        # ``<head>`` would have to be ``<slug>.<N>``; a single segment is
        # not a version dir.
        return None
    if _VERSION_DIR_RE.match(head) is None:
        return None
    return head, tag


@dataclass
class StubConversion:
    """One planned sidecar stub conversion.

    Attributes
    ----------
    sidecar_dir
        The existing ``<slug>.<N>.<tag>/`` directory holding only
        ``review.md`` (the conversion target).
    version_dir
        The version-dir name this critic reviews (e.g. ``meridian-c.7``),
        inferred from the sidecar name. Echoed into the stub's
        ``version_dir`` field.
    critic_id
        The trailing tag (e.g. ``enablement``), inferred from the sidecar
        name. Echoed into the stub's ``critic_id`` field.
    review_filename
        The verbatim-preserved prose filename (always
        :data:`FOREIGN_REVIEW_FILENAME`). Recorded as PRESERVED, never as
        a rename source.
    """

    sidecar_dir: Path
    version_dir: str
    critic_id: str
    review_filename: str = FOREIGN_REVIEW_FILENAME


@dataclass
class AdoptReviewPlan:
    """The (possibly empty) batch of stub conversions for one tree.

    Attributes
    ----------
    directory
        The adopted-tree root the plan was built for.
    conversions
        One :class:`StubConversion` per ``review.md``-only sidecar found.
        Empty when the tree has none (idempotent no-op).
    skipped
        Sidecar dir names left untouched with the reason: already
        recognizable (``_review.json`` present), or holding a prose
        payload that is not ``review.md``. Reported, never converted.
    """

    directory: Path
    conversions: List[StubConversion] = field(default_factory=list)
    skipped: List[tuple] = field(default_factory=list)

    @property
    def is_noop(self) -> bool:
        return not self.conversions


def _scan_adopted_tree(directory: Path) -> List[Path]:
    """Return every ``<slug>.<N>.<tag>/`` sidecar dir under ``directory``.

    Walks the adopted tree: ``<directory>/<slug>/`` thread roots, each
    holding ``<slug>.<N>/`` version dirs and their ``<slug>.<N>.<tag>/``
    critic siblings (the Phase-2 output shape). Also tolerates the
    flat layout (siblings directly under ``directory``) so the mode works
    on a directly-passed thread root too. Returns sidecar dirs only —
    version dirs and bodies are never returned.
    """
    sidecars: List[Path] = []
    seen: set = set()

    def _collect(parent: Path) -> None:
        try:
            children = sorted(parent.iterdir())
        except OSError:
            return
        for child in children:
            if not child.is_dir():
                continue
            if child.name.startswith("."):
                continue  # staging dirs / dotfiles
            if _split_sidecar_name(child.name) is not None:
                rp = child.resolve()
                if rp not in seen:
                    seen.add(rp)
                    sidecars.append(child)

    # Flat: sidecars directly under the passed directory (thread-root case).
    _collect(directory)
    # Nested: <directory>/<slug>/<slug>.N.tag (project-root case).
    try:
        top = sorted(directory.iterdir())
    except OSError:
        top = []
    for child in top:
        if child.is_dir() and not child.name.startswith("."):
            _collect(child)

    sidecars.sort(key=lambda p: str(p.resolve()))
    return sidecars


def build_adopt_review_plan(directory: Path) -> AdoptReviewPlan:
    """Build a stub-conversion :class:`AdoptReviewPlan` for ``directory``.

    Pure planner (no mutations). Scans an already-adopted tree for critic
    sidecar dirs that hold ONLY a single-file ``review.md`` payload —
    those that fail ``critics._has_recognizable_review`` and so stay
    invisible to ``discover_critics`` (the #346 additive contract).

    A directory with no such sidecar yields an EMPTY plan
    (``plan.is_noop``) — re-running on a tree where every sidecar already
    carries ``_review.json`` is a no-op, not an error.

    Parameters
    ----------
    directory
        An adopted-tree root (project root or a single thread root). Names
        are assumed already canonical — this mode runs AFTER
        ``--adopt-family`` / ``--adopt-vn``.

    Raises
    ------
    AdoptReviewError
        When ``directory`` does not exist or is not a directory.
    """
    directory = Path(directory).resolve()
    if not directory.is_dir():
        raise AdoptReviewError(
            f"--adopt-review target {directory} does not exist or is not "
            f"a directory."
        )

    plan = AdoptReviewPlan(directory=directory)

    for sidecar in _scan_adopted_tree(directory):
        # Idempotence + real-review safety: a sidecar that already passes
        # discovery (carries `_review.json` or a complete legacy triple)
        # is never touched.
        if _has_recognizable_review(sidecar):
            plan.skipped.append(
                (sidecar.name, "already recognizable (_review.json present)")
            )
            continue
        review_md = sidecar / FOREIGN_REVIEW_FILENAME
        if not review_md.is_file():
            # A sidecar with neither a recognizable payload nor the
            # expected `review.md` prose — left untouched (we never guess
            # a differently-named prose file).
            plan.skipped.append(
                (sidecar.name, f"no {FOREIGN_REVIEW_FILENAME} payload")
            )
            continue
        plan.conversions.append(
            StubConversion(
                sidecar_dir=sidecar,
                version_dir=_infer_version_dir(sidecar),
                critic_id=_infer_critic_id(sidecar),
            )
        )

    return plan


def build_stub_review(conv: StubConversion) -> Review:
    """Build the honest unscored-foreign stub :class:`Review` for ``conv``.

    Empty ``scores``/``findings``/``critical_flags``; null
    ``total``/``threshold``/``verdict``; ``unscored=True``. NO fabricated
    dimensions. Validates against ``review_schema`` (the ``unscored=True``
    carve-out is the only thing that lets ``scores`` be empty).
    """
    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=conv.version_dir,
        critic_id=conv.critic_id,
        scores=[],
        findings=[],
        critical_flags=[],
        total=None,
        threshold=None,
        verdict=None,
        unscored=True,
    )


def build_provenance_marker(conv: StubConversion) -> dict:
    """Build the ``_meta.json`` foreign-provenance marker for ``conv``.

    The exact shape pinned by the issue #454 curation comment — a reader
    distinguishes an unscored-foreign stub from a real review by this
    marker (``source: foreign-adopted``, ``unscored: true``).
    """
    return {
        "source": PROVENANCE_SOURCE,
        "unscored": True,
        "origin_filename": conv.review_filename,
        "adopted_by": PROVENANCE_ADOPTED_BY,
    }


@dataclass
class AdoptReviewApplyResult:
    """Typed outcome of :func:`apply_adopt_review_plan`.

    Attributes
    ----------
    converted
        Sidecar dir names successfully converted (stub written).
    failed
        ``(sidecar_name, error)`` for any conversion that failed; its dir
        was restored byte-identical.
    """

    converted: List[str] = field(default_factory=list)
    failed: List[tuple] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.failed


def apply_adopt_review_plan(plan: AdoptReviewPlan) -> AdoptReviewApplyResult:
    """Execute a stub-conversion plan (``--apply`` only).

    Each conversion is per-sidecar atomic and verbatim-preserving:

    1. Stage a full replacement dir (leading-dot ``.tmp`` sibling) via
       :func:`anvil.lib.sidecar.staged_sidecar`: copy ``review.md`` into
       the staging dir byte-for-byte, then write ``_review.json`` (the
       stub) and ``_meta.json`` (the provenance marker).
    2. Atomically swap: move the existing sidecar dir aside to a
       leading-dot ``.bak`` sibling (``staged_sidecar`` refuses a
       pre-existing final target), let the context manager rename the
       staging dir into place, then remove the moved-aside backup.
    3. On any failure, the moved-aside original is restored untouched and
       the staging dir is swept; the conversion is recorded as failed.

    Failures in one sidecar do not affect already-converted siblings.
    """
    result = AdoptReviewApplyResult()

    for conv in plan.conversions:
        sidecar = conv.sidecar_dir
        backup = sidecar.parent / f".{sidecar.name}.bak"
        try:
            _convert_one(conv, backup)
            result.converted.append(sidecar.name)
        except BaseException as exc:  # noqa: BLE001 — isolate per sidecar
            # Restore the moved-aside original if the swap left it aside.
            if backup.exists() and not sidecar.exists():
                backup.rename(sidecar)
            elif backup.exists():
                # Both present (failure after rename-in but before backup
                # removal is impossible — that path can't raise — but be
                # defensive): drop the stale backup, keep the live dir.
                shutil.rmtree(backup)
            cleanup_one_staging(sidecar)
            result.failed.append((sidecar.name, str(exc)))

    return result


def _convert_one(conv: StubConversion, backup: Path) -> None:
    """Atomically replace ``conv.sidecar_dir`` with the stub-bearing dir.

    Raises on any failure; the caller restores from ``backup``.
    """
    sidecar = conv.sidecar_dir
    stub = build_stub_review(conv)
    marker = build_provenance_marker(conv)

    # Clear any stale staging from a prior interrupted attempt (parallel-
    # safe: targets only THIS sidecar's staging path).
    cleanup_one_staging(sidecar)

    # Move the live dir aside so the atomic-rename target is free. Every
    # original file travels along in `backup` — the conversion is purely
    # additive and `review.md` (plus anything else already present) is
    # preserved byte-identical.
    if backup.exists():
        shutil.rmtree(backup)
    sidecar.rename(backup)

    try:
        with staged_sidecar(
            final_dir=sidecar,
            required_files=[
                conv.review_filename,
                CANONICAL_REVIEW_FILENAME,
                PROVENANCE_FILENAME,
            ],
            # `sidecar` was just renamed to `backup` two lines above, so
            # staged_sidecar's default orphaned-backup guard (issue #885)
            # would always fire here. Safe to opt out: this driver's own
            # `except BaseException` handler above is guaranteed to run and
            # restores/discards `backup` on any failure — the guard exists
            # for callers with no such handler.
            allow_orphaned_backup=True,
        ) as staging:
            # Re-materialize every original file byte-for-byte (verbatim
            # preservation), then layer the two additive files on top.
            for entry in sorted(backup.iterdir()):
                if entry.is_dir():
                    shutil.copytree(entry, staging / entry.name)
                else:
                    shutil.copy2(entry, staging / entry.name)
            (staging / CANONICAL_REVIEW_FILENAME).write_text(
                stub.model_dump_json(indent=2) + "\n", encoding="utf-8"
            )
            (staging / PROVENANCE_FILENAME).write_text(
                json.dumps(marker, indent=2) + "\n", encoding="utf-8"
            )
    except BaseException:
        # Staging failed or the rename-in raised: the live dir is still
        # aside at `backup`. Re-raise so the caller restores it.
        raise

    # Swap succeeded — drop the moved-aside original.
    shutil.rmtree(backup)


# ---------------------------------------------------------------------------
# Phase 3b: operator-driven LLM rescore of stubs (issue #507)
# ---------------------------------------------------------------------------


# Stamped into the rescored ``_meta.json`` to record that this review was
# scored FROM a foreign-adopted stub (the lineage breadcrumb the issue #507
# curation comment asks for). The original ``source: foreign-adopted`` is
# preserved alongside, so the full provenance chain is legible.
RESCORED_FROM = PROVENANCE_SOURCE  # "foreign-adopted"
RESCORED_BY = "anvil:project-migrate#507"


def _is_foreign_stub(sidecar: Path) -> bool:
    """Return True iff ``sidecar`` carries a Phase-3a foreign stub.

    The dual marker (issue #454): ``_review.json`` with ``unscored: true``
    AND ``_meta.json`` ``source: foreign-adopted``. A real review (no
    ``unscored``), an already-rescored sidecar (``unscored: false``), or a
    non-adopted ``_review.json`` is NOT a stub.
    """
    review_path = sidecar / CANONICAL_REVIEW_FILENAME
    meta_path = sidecar / PROVENANCE_FILENAME
    if not review_path.is_file() or not meta_path.is_file():
        return False
    try:
        review = json.loads(review_path.read_text(encoding="utf-8"))
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return (
        isinstance(review, dict)
        and review.get("unscored") is True
        and isinstance(meta, dict)
        and meta.get("source") == PROVENANCE_SOURCE
    )


@dataclass
class RescoreTarget:
    """One planned stub → scored-review rescore.

    Attributes
    ----------
    sidecar_dir
        The ``<slug>.{N}.<tag>/`` stub sidecar to rescore.
    version_dir
        The version-dir name the critic reviews (from the stub's
        ``_review.json``). Echoed into the rescored ``Review.version_dir``.
    critic_id
        The trailing tag (the stub's ``critic_id``).
    review_filename
        The verbatim-preserved prose payload (always ``review.md``).
    skill
        The resolved owning skill (e.g. ``"memo"``). Surfaced in the
        report; used only to look up the rubric.
    rubric
        The resolved target :class:`rescore_rubrics.RubricIdentity`. The
        operator/LLM scores ``review.md`` against this; the writer stamps
        its three fields.
    skill_source
        Where the skill inference came from (``"brief"`` /
        ``"body-filename"``) — operator-facing provenance.
    """

    sidecar_dir: Path
    version_dir: str
    critic_id: str
    skill: str
    rubric: RubricIdentity
    skill_source: str
    review_filename: str = FOREIGN_REVIEW_FILENAME


@dataclass
class RescorePlan:
    """The (possibly empty) batch of rescores for one adopted tree.

    Attributes
    ----------
    directory
        The adopted-tree root the plan was built for.
    targets
        One :class:`RescoreTarget` per foreign stub whose rubric resolved.
        Empty when the tree has no resolvable stub (idempotent no-op).
    skipped
        ``(sidecar_name, reason)`` for sidecars left untouched: not a stub
        (real review / already rescored), or a stub whose rubric could not
        be resolved (the honesty guard — never guessed).
    """

    directory: Path
    targets: List[RescoreTarget] = field(default_factory=list)
    skipped: List[tuple] = field(default_factory=list)

    @property
    def is_noop(self) -> bool:
        return not self.targets


def build_rescore_plan(directory: Path) -> RescorePlan:
    """Build a :class:`RescorePlan` of foreign stubs to rescore.

    Pure planner (no mutations). Scans an already-adopted tree for sidecars
    carrying a Phase-3a stub (``_review.json`` ``unscored: true`` +
    ``_meta.json`` ``source: foreign-adopted``) and resolves the target
    anvil rubric per stub (BRIEF ``documents:`` → body-filename fallback).

    A stub whose rubric cannot be resolved is SKIPPED with an
    operator-visible note (the honesty guard) — never assigned a guessed
    rubric. A tree with no resolvable stub yields an EMPTY plan
    (``plan.is_noop``): re-running on a fully-rescored tree is a no-op, and
    running on a tree with no Phase-3a stub is an empty plan, not an error.

    Raises
    ------
    AdoptReviewError
        When ``directory`` does not exist or is not a directory.
    """
    directory = Path(directory).resolve()
    if not directory.is_dir():
        raise AdoptReviewError(
            f"--adopt-review --rescore target {directory} does not exist "
            f"or is not a directory."
        )

    # Resolve the slug→skill map ONCE for the whole tree (BRIEF walk).
    brief_skill_map = _build_brief_skill_map(directory)

    plan = RescorePlan(directory=directory)

    for sidecar in _scan_adopted_tree(directory):
        if not _is_foreign_stub(sidecar):
            plan.skipped.append(
                (sidecar.name, "not a foreign stub (real review or already rescored)")
            )
            continue
        rubric, skill, source = resolve_rubric_for_sidecar(
            sidecar, brief_skill_map=brief_skill_map
        )
        if rubric is None:
            plan.skipped.append(
                (
                    sidecar.name,
                    "rubric could not be resolved (no BRIEF entry, no "
                    "body-filename match) — SKIPPED, never guessed",
                )
            )
            continue
        plan.targets.append(
            RescoreTarget(
                sidecar_dir=sidecar,
                version_dir=_infer_version_dir(sidecar),
                critic_id=_infer_critic_id(sidecar),
                skill=skill,
                rubric=rubric,
                skill_source=source,
            )
        )

    return plan


@dataclass
class ScoredReviewInput:
    """Operator/LLM-supplied score set for one rescore target.

    The slash-command runtime reads the verbatim ``review.md`` + the
    resolved rubric and produces this — the ONLY judgment-laden input the
    Python harness consumes. It carries the per-dimension scores, optional
    findings, and optional critical flags. The harness derives ``total`` /
    ``verdict`` deterministically from these against the target rubric (so
    the operator cannot accidentally desync the verdict from the scores).

    Attributes
    ----------
    sidecar_name
        The target sidecar's directory name — the key that pairs this
        input to its :class:`RescoreTarget`.
    scores
        Per-dimension :class:`anvil.lib.review_schema.Score` objects (the
        full scorecard). Non-empty — flipping ``unscored`` to ``False``
        REQUIRES a populated scorecard per the #454 schema contract.
    findings
        Optional itemized findings (default empty).
    critical_flags
        Optional top-level critical flags (default empty). Any non-empty
        list forces a ``BLOCK`` verdict.
    """

    sidecar_name: str
    scores: List[Score]
    findings: List = field(default_factory=list)
    critical_flags: List = field(default_factory=list)


def build_scored_review(
    target: RescoreTarget, scored: ScoredReviewInput
) -> Review:
    """Build the scored :class:`Review` for ``target`` from ``scored``.

    Flips ``unscored`` to ``False``, populates ``scores`` / ``findings`` /
    ``critical_flags``, stamps the rubric id, and derives ``total`` /
    ``threshold`` / ``verdict`` deterministically:

    - ``total`` = sum of non-null per-dimension scores.
    - ``threshold`` = the rubric's ``advance_threshold``.
    - ``verdict`` = ``BLOCK`` if any critical flag (or any
      ``Score.critical``); else ``ADVANCE`` if ``total >= threshold``;
      else ``REVISE``.

    Raises
    ------
    AdoptReviewError
        When ``scored.scores`` is empty (the #454 schema contract forbids
        an empty scorecard once ``unscored`` is ``False``).
    """
    if not scored.scores:
        raise AdoptReviewError(
            f"rescore for {target.sidecar_dir.name} supplied no scores; "
            f"a scored review REQUIRES a non-empty scorecard (flipping "
            f"unscored=False with empty scores fails schema validation)."
        )

    total = sum(s.score for s in scored.scores if s.score is not None)
    threshold = target.rubric.advance_threshold
    has_critical = bool(scored.critical_flags) or any(
        s.critical for s in scored.scores
    )
    if has_critical:
        verdict = Verdict.BLOCK
    elif total >= threshold:
        verdict = Verdict.ADVANCE
    else:
        verdict = Verdict.REVISE

    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=target.version_dir,
        critic_id=target.critic_id,
        rubric=target.rubric.id,
        scores=scored.scores,
        findings=scored.findings,
        critical_flags=scored.critical_flags,
        total=total,
        threshold=threshold,
        verdict=verdict,
        unscored=False,
    )


def build_rescored_marker(target: RescoreTarget) -> dict:
    """Build the rescored ``_meta.json`` marker for ``target``.

    Flips ``unscored`` to ``False``, stamps the v0.4.0 per-review rubric
    fields (``rubric_id`` / ``rubric_total`` / ``advance_threshold``), and
    records lineage: ``rescored_from: foreign-adopted`` while retaining
    ``source: foreign-adopted`` + ``origin_filename`` so the full
    provenance chain (foreign → stub → scored) stays legible.
    """
    return {
        "source": PROVENANCE_SOURCE,
        "unscored": False,
        "origin_filename": target.review_filename,
        "adopted_by": PROVENANCE_ADOPTED_BY,
        "rescored_from": RESCORED_FROM,
        "rescored_by": RESCORED_BY,
        "rubric_id": target.rubric.id,
        "rubric_total": target.rubric.total,
        "advance_threshold": target.rubric.advance_threshold,
    }


@dataclass
class RescoreApplyResult:
    """Typed outcome of :func:`apply_rescore_plan`.

    Attributes
    ----------
    rescored
        Sidecar dir names successfully rescored (scored review written).
    skipped_no_input
        Sidecar dir names in the plan for which the caller supplied no
        :class:`ScoredReviewInput` (the LLM step produced nothing) — left
        as honest stubs, untouched.
    failed
        ``(sidecar_name, error)`` for any rescore that failed; its dir was
        restored byte-identical (still the original stub).
    """

    rescored: List[str] = field(default_factory=list)
    skipped_no_input: List[str] = field(default_factory=list)
    failed: List[tuple] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.failed


def apply_rescore_plan(
    plan: RescorePlan, scored_reviews: dict
) -> RescoreApplyResult:
    """Execute a rescore plan (``--rescore --apply`` only).

    ``scored_reviews`` maps a target sidecar name → its
    :class:`ScoredReviewInput` (produced by the operator/LLM step in the
    slash-command runtime). A target with no entry is left as an honest
    stub (recorded in ``skipped_no_input``) — the harness NEVER fabricates
    scores.

    Each rescore is per-sidecar atomic and verbatim-preserving — it reuses
    the exact :func:`_rescore_one` staged/backup/swap pattern so
    ``review.md`` stays byte-identical and the write is crash-safe via
    ``anvil/lib/sidecar.py::staged_sidecar``. On any failure the original
    stub is restored untouched.
    """
    result = RescoreApplyResult()

    for target in plan.targets:
        sidecar = target.sidecar_dir
        scored = scored_reviews.get(sidecar.name)
        if scored is None:
            result.skipped_no_input.append(sidecar.name)
            continue
        backup = sidecar.parent / f".{sidecar.name}.bak"
        try:
            _rescore_one(target, scored, backup)
            result.rescored.append(sidecar.name)
        except BaseException as exc:  # noqa: BLE001 — isolate per sidecar
            if backup.exists() and not sidecar.exists():
                backup.rename(sidecar)
            elif backup.exists():
                shutil.rmtree(backup)
            cleanup_one_staging(sidecar)
            result.failed.append((sidecar.name, str(exc)))

    return result


def _rescore_one(
    target: RescoreTarget, scored: ScoredReviewInput, backup: Path
) -> None:
    """Atomically replace ``target.sidecar_dir`` with the scored review.

    Mirrors :func:`_convert_one` exactly (staged/backup/swap), but writes a
    SCORED ``_review.json`` (``unscored=False``) + a rescored ``_meta.json``
    (lineage + rubric stamping). ``review.md`` and any other original file
    travel along byte-identical. Raises on any failure; the caller restores
    from ``backup``.
    """
    sidecar = target.sidecar_dir
    review = build_scored_review(target, scored)
    marker = build_rescored_marker(target)

    cleanup_one_staging(sidecar)

    if backup.exists():
        shutil.rmtree(backup)
    sidecar.rename(backup)

    with staged_sidecar(
        final_dir=sidecar,
        required_files=[
            target.review_filename,
            CANONICAL_REVIEW_FILENAME,
            PROVENANCE_FILENAME,
        ],
        # See the matching comment in _convert_one: `sidecar` was just
        # renamed to `backup` above, so the default orphaned-backup guard
        # (issue #885) would always fire here. This driver's caller-level
        # `except BaseException` handler restores/discards `backup` on any
        # failure, so opting out is safe.
        allow_orphaned_backup=True,
    ) as staging:
        for entry in sorted(backup.iterdir()):
            if entry.name in (CANONICAL_REVIEW_FILENAME, PROVENANCE_FILENAME):
                # Overwritten below with the scored payload — do NOT copy
                # the stub versions across.
                continue
            if entry.is_dir():
                shutil.copytree(entry, staging / entry.name)
            else:
                shutil.copy2(entry, staging / entry.name)
        (staging / CANONICAL_REVIEW_FILENAME).write_text(
            review.model_dump_json(indent=2) + "\n", encoding="utf-8"
        )
        (staging / PROVENANCE_FILENAME).write_text(
            json.dumps(marker, indent=2) + "\n", encoding="utf-8"
        )

    shutil.rmtree(backup)


__all__ = [
    "AdoptReviewApplyResult",
    "AdoptReviewError",
    "AdoptReviewPlan",
    "RescoreApplyResult",
    "RescorePlan",
    "RescoreTarget",
    "ScoredReviewInput",
    "StubConversion",
    "apply_adopt_review_plan",
    "apply_rescore_plan",
    "build_adopt_review_plan",
    "build_provenance_marker",
    "build_rescore_plan",
    "build_rescored_marker",
    "build_scored_review",
    "build_stub_review",
    "FOREIGN_REVIEW_FILENAME",
    "PROVENANCE_FILENAME",
]
