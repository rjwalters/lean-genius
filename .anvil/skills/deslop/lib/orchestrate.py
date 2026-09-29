"""Iterate-until-converged orchestration primitives for `anvil:deslop` (issue #898).

This module supplies every **deterministic** primitive the
`commands/deslop.md` draft -> lint -> critique -> revise loop composes:

- A scratchpad **thread** on disk, versioned exactly like every other
  anvil artifact (``<thread>.{N}/`` + critic siblings
  ``<thread>.{N}.<tag>/``) so the loop can reuse the existing
  ``anvil.lib.critics`` discovery/aggregation machinery unmodified rather
  than reimplementing it.
- The deterministic **lint pass** (``anvil.lib.rhetoric_lint.lint_rhetoric``),
  honoring a consumer's declared ``voice.rhetoric_rules`` via
  ``anvil.lib.project_brief.resolve_rhetoric_rules`` when the input
  originates from a project with a ``BRIEF.md``.
- **Voice-grounding resolution** (``anvil.lib.project_brief.resolve_voice_docs``)
  so the critique step can honor STYLE_GUIDE.md / VOCABULARY.md / VALUES
  when the consumer has them — the #461 voice contract.
- **Critic-review IO** against the canonical ``_review.json`` schema
  (``anvil.lib.review_schema``), so the LLM-driven critique step in
  ``commands/deslop.md`` has a typed, validated shape to write into
  rather than hand-rolled JSON.
- **Convergence** (``anvil.lib.convergence.decide_termination`` via
  ``anvil.lib.critics.aggregate``) — the same iterate-until-converged
  machinery every other anvil lifecycle skill already uses. This module
  does NOT reimplement convergence logic.
- **Emission**: cleaned text + per-change rationale + (for file inputs) a
  ready-to-apply diff. `anvil:deslop` NEVER writes to the ingested
  source — every write here lands under the scratchpad thread directory.
- The **deterministic no-fabrication gate**
  (``anvil.skills.deslop.lib.no_fabrication.diff_no_fabrication``, issue
  #922) diffing iteration N against N+1 for introduced numerals / proper
  nouns / citation-shaped tokens absent from the prior iteration, every
  resolved voice-grounding doc, and any explicit operator-supplied detail.

What this module deliberately does NOT do: score rhetorical economy or
voice adherence itself. That is the judgment call `commands/deslop.md`
delegates to the LLM performing the critique pass — this module only
gives it somewhere typed and convergent to land the verdict.
"""

from __future__ import annotations

import difflib
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Sequence, Tuple, Union

from anvil.lib.convergence import decide_termination
from anvil.lib.critics import aggregate, discover_critics, load_review
from anvil.lib.project_brief import resolve_rhetoric_rules, resolve_voice_docs
from anvil.lib.review_schema import (
    AggregatedReview,
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
    Verdict,
)
from anvil.lib.rhetoric_lint import RhetoricLintResult, lint_rhetoric

from .ingest import IngestedItem
from .no_fabrication import NoFabricationResult, diff_no_fabrication

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# deslop's mini rubric: two dims, mirroring the dim-9 "Rhetorical economy"
# critic pattern already used by memo/essay, plus a voice-adherence sibling
# dim for when the consumer has declared voice-grounding docs. deslop is a
# utility skill (no rubric.md, no per-consumer overrides) so this lives here
# as a fixed constant rather than a venue-pinned rubric overlay.
RHETORICAL_ECONOMY_DIM = "rhetorical_economy"
VOICE_ADHERENCE_DIM = "voice_adherence"

# 16/20 = 80%, matching essay's 35/44 (~80%) general-tier advance bar. This
# is the default when BOTH dims are active (a critic scored voice_adherence
# because voice_context() resolved grounding docs). When voice_adherence is
# legitimately unowned (score=None — no voice docs to judge against), the
# achievable max drops to the 10-point rhetorical_economy dim alone, so
# new_review() scales the default threshold down to
# RHETORICAL_ECONOMY_ONLY_THRESHOLD (still 80%) rather than pinning an
# unreachable 16/10.
DEFAULT_THRESHOLD = 16
RHETORICAL_ECONOMY_ONLY_THRESHOLD = round(0.8 * 10)  # 8
DEFAULT_MAX_ITERATIONS = 4

DEFAULT_CRITIC_TAG = "critic"


# ---------------------------------------------------------------------------
# Scratchpad thread management
# ---------------------------------------------------------------------------

_SLUG_RE = re.compile(r"[^a-z0-9]+")


def slugify(label: str) -> str:
    """Derive a filesystem-safe thread slug from an ingested item's label."""
    stem = Path(label).stem or label
    slug = _SLUG_RE.sub("-", stem.lower()).strip("-")
    return slug or "prose"


def init_thread(scratch_root: Union[str, Path], slug: str) -> Path:
    """Create (or reuse) the scratchpad thread directory ``<scratch_root>/<slug>/``."""
    thread_dir = Path(scratch_root) / slug
    thread_dir.mkdir(parents=True, exist_ok=True)
    return thread_dir


def version_dir_name(thread_dir: Path, n: int) -> str:
    """Return the bare ``<slug>.<n>`` name (no path), echoed onto ``Review.version_dir``."""
    return f"{thread_dir.name}.{n}"


def version_dir(thread_dir: Path, n: int) -> Path:
    return thread_dir / version_dir_name(thread_dir, n)


def write_version(thread_dir: Path, n: int, body: str) -> Path:
    """Write iteration ``n``'s prose to ``<thread_dir>/<slug>.<n>/<slug>.md``.

    Versions are immutable once written by convention (matching every
    other anvil skill); this function does not enforce that, it simply
    writes.
    """
    vdir = version_dir(thread_dir, n)
    vdir.mkdir(parents=True, exist_ok=True)
    (vdir / f"{thread_dir.name}.md").write_text(body, encoding="utf-8")
    return vdir


def read_version(thread_dir: Path, n: int) -> str:
    vdir = version_dir(thread_dir, n)
    return (vdir / f"{thread_dir.name}.md").read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Deterministic lint pass
# ---------------------------------------------------------------------------


def lint_body(
    body: str,
    project_dir: Optional[Union[str, Path]] = None,
) -> RhetoricLintResult:
    """Run the deterministic rhetoric lint over ``body``.

    When ``project_dir`` is given and its ``BRIEF.md`` declares
    ``voice.rhetoric_rules``, that consumer rule file is resolved via
    :func:`anvil.lib.project_brief.resolve_rhetoric_rules` and forwarded
    as ``extra_rules_path`` — the direct-call kwarg essay-review uses
    (issue #479), not the render-gate's ``rhetoric_rules_path=``. A
    declared-but-missing file is forwarded too (its unresolved declared
    path), so ``lint_rhetoric``'s graceful-degrade surfaces the broken
    declaration as a warning finding rather than silently falling back.
    No ``project_dir`` (or no declaration) falls back to the framework
    default rule set — never a crash.
    """
    extra_rules_path: Optional[str] = None
    if project_dir is not None:
        pdir = Path(project_dir)
        resolved = resolve_rhetoric_rules(pdir)
        if resolved is not None:
            if resolved.paths:
                extra_rules_path = resolved.paths[0]
            elif resolved.missing:
                # Broken declaration: forward the unresolved declared path
                # anyway so lint_rhetoric's own graceful-degrade names it.
                extra_rules_path = str(pdir / resolved.declared)
    return lint_rhetoric(body, extra_rules_path=extra_rules_path)


# ---------------------------------------------------------------------------
# Voice-grounding resolution
# ---------------------------------------------------------------------------


def voice_context(
    project_dir: Optional[Union[str, Path]] = None,
    *,
    exclude_self_slug: Optional[str] = None,
):
    """Resolve the consumer's voice-grounding docs (values/style/vocab/corpus).

    Returns ``[]`` (the documented "tier INACTIVE" shape) when
    ``project_dir`` is ``None`` — deslop routinely runs against prose that
    has no owning anvil project at all (a README fragment, pasted site
    copy). When a project IS given, delegates directly to
    :func:`anvil.lib.project_brief.resolve_voice_docs` — never raises on a
    missing/malformed BRIEF or a broken declared doc.
    """
    if project_dir is None:
        return []
    return resolve_voice_docs(Path(project_dir), exclude_self_slug=exclude_self_slug)


# ---------------------------------------------------------------------------
# Deterministic no-fabrication gate (issue #922)
# ---------------------------------------------------------------------------


def check_no_fabrication(
    thread_dir: Path,
    n: int,
    *,
    voice_docs: Optional[Sequence[object]] = None,
    extra_allowed_tokens: Optional[Sequence[str]] = None,
) -> NoFabricationResult:
    """Diff iteration ``n`` against iteration ``n + 1`` for fabricated
    numerals / proper nouns / citation-shaped tokens (issue #922).

    Thin wrapper over :func:`anvil.skills.deslop.lib.no_fabrication.diff_no_fabrication`
    that reads both versions off disk via :func:`read_version` and flattens
    ``voice_docs`` (the return value of :func:`voice_context` — a list of
    ``ResolvedVoiceDoc``-shaped objects with a ``.paths`` attribute) into
    the bare path list the pure diff function expects. A plain string/Path
    is also accepted per element, so a caller that already has bare paths
    does not need to fake the ``ResolvedVoiceDoc`` shape.

    Call this **after** step 3e writes iteration ``n + 1`` — the findings
    on the returned :class:`NoFabricationResult` are evidence the *next*
    iteration's step 3c critique should cite or explicitly decide not to
    act on, exactly like :func:`lint_body`'s findings. This is advisory
    evidence, not a hard block: nothing in this module raises or forces a
    verdict.
    """
    prior = read_version(thread_dir, n)
    revised = read_version(thread_dir, n + 1)

    voice_doc_paths: List[str] = []
    for doc in voice_docs or ():
        paths = getattr(doc, "paths", None)
        if paths:
            voice_doc_paths.extend(paths)
        elif isinstance(doc, (str, Path)):
            voice_doc_paths.append(str(doc))

    return diff_no_fabrication(
        prior,
        revised,
        voice_doc_paths=voice_doc_paths,
        extra_allowed_tokens=extra_allowed_tokens,
    )


# ---------------------------------------------------------------------------
# Critic-review IO (canonical _review.json)
# ---------------------------------------------------------------------------


def new_review(
    *,
    version_dir_name: str,  # the bare "<slug>.<n>" string, e.g. version_dir_name(thread_dir, n)
    critic_id: str = DEFAULT_CRITIC_TAG,
    rhetorical_economy: Optional[int],
    rhetorical_economy_justification: Optional[str] = None,
    rhetorical_economy_fix: Optional[str] = None,
    voice_adherence: Optional[int],
    voice_adherence_justification: Optional[str] = None,
    voice_adherence_fix: Optional[str] = None,
    findings: Optional[List[Finding]] = None,
    critical_flags: Optional[List[CriticalFlag]] = None,
    model: Optional[str] = None,
    threshold: Optional[int] = None,
) -> Review:
    """Build a typed :class:`Review` for deslop's two-dimension mini rubric.

    ``voice_adherence`` should be ``None`` (unowned dimension, per the
    schema's mean-of-non-null aggregation contract) when
    :func:`voice_context` resolved no grounding docs — there is nothing to
    judge voice fidelity against, and ``None`` is the documented "this
    critic does not own the dimension" value (never fabricate a 0).

    ``threshold`` defaults to :data:`DEFAULT_THRESHOLD` (16/20) when both
    dims are scored, or :data:`RHETORICAL_ECONOMY_ONLY_THRESHOLD` (8/10)
    when ``voice_adherence`` is ``None`` — an unowned dim must not make
    the achievable max unreachable. Pass an explicit ``threshold`` to
    override either default.
    """
    if threshold is None:
        active_max = (10 if rhetorical_economy is not None else 0) + (
            10 if voice_adherence is not None else 0
        )
        threshold = round(0.8 * active_max) if active_max else DEFAULT_THRESHOLD

    scores = [
        Score(
            dimension=RHETORICAL_ECONOMY_DIM,
            score=rhetorical_economy,
            max=10,
            justification=rhetorical_economy_justification,
            fix=rhetorical_economy_fix,
        ),
        Score(
            dimension=VOICE_ADHERENCE_DIM,
            score=voice_adherence,
            max=10,
            justification=voice_adherence_justification,
            fix=voice_adherence_fix,
        ),
    ]
    return Review(
        kind=Kind.JUDGMENT,
        version_dir=version_dir_name,
        critic_id=critic_id,
        model=model,
        scores=scores,
        findings=findings or [],
        critical_flags=critical_flags or [],
        threshold=threshold,
    )


def write_critic_review(
    thread_dir: Path,
    n: int,
    review: Review,
    *,
    tag: str = DEFAULT_CRITIC_TAG,
) -> Path:
    """Write ``review`` to ``<thread_dir>/<slug>.<n>.<tag>/_review.json``.

    The sibling directory shape matches
    ``anvil.lib.critics.discover_critics``'s ``<version_dir>.<tag>/``
    contract exactly, so :func:`aggregate_reviews` (and any other
    ``critics.py`` consumer) can discover it unmodified.
    """
    critic_dir = thread_dir / f"{version_dir_name(thread_dir, n)}.{tag}"
    critic_dir.mkdir(parents=True, exist_ok=True)
    payload = review.model_dump(mode="json")
    (critic_dir / "_review.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return critic_dir


def aggregate_reviews(thread_dir: Path, n: int) -> AggregatedReview:
    """Discover every critic sibling for iteration ``n`` and aggregate them.

    Thin composition of ``anvil.lib.critics.discover_critics`` +
    ``load_review`` + ``aggregate`` — no convergence/aggregation logic is
    reimplemented here. Raises
    ``anvil.lib.critics.CriticDiscoveryError`` (via ``aggregate``'s
    ``ValueError`` on an empty list — surfaced as-is) when no critic
    sibling has been written yet for this iteration.
    """
    vdir = version_dir(thread_dir, n)
    critic_dirs = discover_critics(vdir)
    reviews = [load_review(d) for d in critic_dirs]
    return aggregate(reviews)


def decide_next(
    agg: AggregatedReview,
    history: List[Optional[int]],
    iteration: int,
    *,
    max_iterations: int = DEFAULT_MAX_ITERATIONS,
    threshold: Optional[int] = None,
    window: int = 1,
    lookback: int = 2,
) -> Tuple[Verdict, str]:
    """Decide ADVANCE / REVISE / BLOCK / STALLED for the next loop step.

    Thin wrapper over ``anvil.lib.convergence.decide_termination`` — the
    same convergence primitive every other anvil lifecycle skill uses.
    ``history`` is the caller-maintained list of per-iteration aggregated
    totals (append ``agg.total`` after each :func:`aggregate_reviews`
    call); ``iteration`` is 1-indexed.
    """
    eff_threshold = threshold if threshold is not None else agg.threshold
    return decide_termination(
        history=history,
        threshold=eff_threshold,
        iteration=iteration,
        max_iterations=max_iterations,
        window=window,
        lookback=lookback,
        critical_flags=list(agg.critical_flags),
    )


# ---------------------------------------------------------------------------
# Emission: cleaned text + rationale + diff. NEVER touches the source.
# ---------------------------------------------------------------------------


@dataclass
class EmitResult:
    thread_dir: Path
    emit_dir: Path
    cleaned_text_path: Path
    rationale_path: Path
    diff_path: Optional[Path]
    diff: str
    origin: Optional[str] = field(default=None)


def unified_diff_text(original_prose: str, revised_prose: str, *, item: IngestedItem) -> str:
    """Build a unified diff of ``original_prose`` -> ``revised_prose``.

    For a markdown/plain-text file input, ``original_prose`` is expected
    to be ``item.original_text`` (the raw file content — extracted prose
    IS the file body for those kinds), so the diff is literally
    patch-applicable to the source file. For an HTML file input,
    ``original_prose`` is the *extracted* text (``item.prose``), NOT the
    raw HTML — this v1 does not reconstruct HTML, so the diff is between
    extracted-text-then and cleaned-text-now; the header says so
    explicitly, and the operator re-applies the wording change into the
    HTML source by hand (never auto-applied — see module docstring).
    """
    if item.origin_kind == "html-file":
        fromfile = f"a/{item.label} (extracted text — apply manually to the HTML source)"
        tofile = f"b/{item.label} (cleaned text)"
    else:
        fromfile = f"a/{item.label}"
        tofile = f"b/{item.label}"
    diff = difflib.unified_diff(
        original_prose.splitlines(keepends=True),
        revised_prose.splitlines(keepends=True),
        fromfile=fromfile,
        tofile=tofile,
    )
    return "".join(diff)


def emit(
    thread_dir: Path,
    item: IngestedItem,
    final_prose: str,
    rationale: List[str],
) -> EmitResult:
    """Emit the cleaned text + rationale + (for file inputs) a diff.

    Writes ONLY under ``<thread_dir>/emit/`` — never back to
    ``item.origin``. The operator applies ``changes.diff`` (when present)
    to the source file themselves; this function does not touch it.
    """
    emit_dir = thread_dir / "emit"
    emit_dir.mkdir(parents=True, exist_ok=True)

    cleaned_path = emit_dir / "cleaned.txt"
    cleaned_path.write_text(final_prose, encoding="utf-8")

    rationale_path = emit_dir / "rationale.md"
    if rationale:
        body = "# Deslop rationale\n\n" + "\n".join(f"- {line}" for line in rationale) + "\n"
    else:
        body = "# Deslop rationale\n\n_No changes were necessary._\n"
    rationale_path.write_text(body, encoding="utf-8")

    diff_text = ""
    diff_path: Optional[Path] = None
    if item.origin is not None:
        baseline = item.original_text if item.origin_kind != "html-file" else item.prose
        diff_text = unified_diff_text(baseline, final_prose, item=item)
        diff_path = emit_dir / "changes.diff"
        diff_path.write_text(diff_text, encoding="utf-8")

    return EmitResult(
        thread_dir=thread_dir,
        emit_dir=emit_dir,
        cleaned_text_path=cleaned_path,
        rationale_path=rationale_path,
        diff_path=diff_path,
        diff=diff_text,
        origin=item.origin,
    )


__all__ = [
    "RHETORICAL_ECONOMY_DIM",
    "VOICE_ADHERENCE_DIM",
    "DEFAULT_THRESHOLD",
    "RHETORICAL_ECONOMY_ONLY_THRESHOLD",
    "DEFAULT_MAX_ITERATIONS",
    "DEFAULT_CRITIC_TAG",
    "slugify",
    "init_thread",
    "version_dir_name",
    "version_dir",
    "write_version",
    "read_version",
    "lint_body",
    "voice_context",
    "check_no_fabrication",
    "new_review",
    "write_critic_review",
    "aggregate_reviews",
    "decide_next",
    "EmitResult",
    "unified_diff_text",
    "emit",
]
