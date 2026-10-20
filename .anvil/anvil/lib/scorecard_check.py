"""Deterministic scorecard arithmetic validation (issue #392).

The cheapest possible pre-flight gate: validate the *emitted* scorecard
against the *stamped* rubric. The existing typed bounds checks
(``review_schema.Score._validate_score_bounds``,
``rubric.Rubric._validate_weight_sum``) only fire on ``_review.json``
payloads and rubric YAML respectively — never on the memo prose triple
(``verdict.md`` + ``scoring.md`` + ``comments.md``) where the canary's
48-weight/44-total scorecard lived undetected for a full revision cycle
(a ``44/44`` verdict whose own ``scoring.md`` weight column summed to 48).

This module fills that gap by composing the existing legacy-adapter
parsers in ``anvil/lib/critics.py`` (``parse_memo_scoring_table``,
``parse_memo_verdict_total``, ``parse_memo_verdict_decision``) with the
per-review rubric stamps (``rubric_id`` / ``rubric_total`` /
``advance_threshold`` in ``_meta.json``, the issue #346 contract
documented in ``anvil/lib/snippets/scorecard_kind.md``).

Checks (finding codes)
----------------------

- ``weights_sum_mismatch`` — the sum of per-dimension weights in the
  scorecard does not equal the **effective pool**, where effective pool
  = stamped ``rubric_total`` + the sum of ``weight_adjustments`` deltas
  when an artifact-type overlay applies (e.g. memo's ``vision-document``
  overlay reduces the pool from 44 to 38). The canary case:
  ``weights_sum_mismatch: 48 != 44``.
- ``score_out_of_bounds`` — a per-dimension score is not a non-negative
  integer ≤ its per-dimension weight.
- ``total_mismatch`` — the declared total (``verdict.md``'s
  ``Total: X/Y``) does not equal the sum of per-dimension scores.
- ``advance_inconsistent`` — ``advance: true`` while the total is below
  the stamped ``advance_threshold`` OR critical flags are present.
- ``pool_unstamped`` — info-level: ``_meta.json`` lacks the #346 stamps
  (legacy pre-#346 review), so there is no pool of record. The other
  checks still run (they are internal to the scorecard); the weights-sum
  check degrades to this info finding.
- ``parse_error`` — the scorecard could not be parsed into a typed
  ``Review`` for a reason other than a per-dimension bounds violation
  (e.g. an empty scoring table). A malformed scorecard must produce
  findings, never an unhandled exception.

Failure behavior (the consumer contract)
-----------------------------------------

- **Write time** (memo-review step 7b, the pilot consumer): findings are
  deterministic arithmetic — the reviewer corrects its own scorecard and
  re-runs the check. If findings persist, ``advance`` is forced false
  via the existing critical-flag pathway (``Scorecard arithmetic
  (lint)`` in ``verdict.md``). A malformed scorecard must never gate the
  state machine to READY.
- **Read time** (``memo-revise`` step 6, ``anvil:rubric-rebackport`` —
  follow-on consumers): the sidecar is immutable; callers record the
  findings and treat the sidecar's verdict as **advisory** — do not
  mutate the sidecar, do not let the malformed verdict drive ADVANCE.

The core check is a **pure function** of ``(Review, stamps)`` — no
filesystem access, mirroring ``critics.aggregate``. The filesystem
convenience ``check_review_dir`` loads via ``critics.load_review``,
reads the stamps from ``_meta.json``, reads any overlay-adjusted pool
from ``_summary.md``'s ``rubric_overlay.weight_adjustments`` block, and
converts ``pydantic.ValidationError`` into findings rather than
crashing.
"""

from __future__ import annotations

import json
import re
import warnings
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

from pydantic import ValidationError

from anvil.lib.critics import load_review, parse_memo_verdict_decision
from anvil.lib.review_schema import Review, Verdict


# Finding codes (stable identifiers; consumers grep for these).
WEIGHTS_SUM_MISMATCH = "weights_sum_mismatch"
SCORE_OUT_OF_BOUNDS = "score_out_of_bounds"
TOTAL_MISMATCH = "total_mismatch"
ADVANCE_INCONSISTENT = "advance_inconsistent"
POOL_UNSTAMPED = "pool_unstamped"
PARSE_ERROR = "parse_error"

# Severities. "error" findings are write-time hard failures / read-time
# advisory-verdict triggers; "info" findings are record-only.
SEVERITY_ERROR = "error"
SEVERITY_INFO = "info"


@dataclass(frozen=True)
class ScorecardFinding:
    """One deterministic arithmetic finding against an emitted scorecard.

    - ``code``: one of the module-level finding-code constants.
    - ``severity``: ``"error"`` or ``"info"``.
    - ``detail``: the compact arithmetic core (e.g. ``"48 != 44"``) —
      the piece that lands in ``_meta.json.scorecard_lint`` summaries.
    - ``message``: the full human-readable diagnostic.
    """

    code: str
    severity: str
    detail: str
    message: str

    @property
    def compact(self) -> str:
        """The ``_meta.json``-summary form, e.g. ``weights_sum_mismatch: 48 != 44``."""
        return f"{self.code}: {self.detail}"


def check_scorecard(
    review: Review,
    *,
    rubric_total: Optional[int],
    advance_threshold: Optional[int],
    weight_adjustments: Optional[Dict[str, int]] = None,
    advance: Optional[bool] = None,
) -> List[ScorecardFinding]:
    """Pure function: validate a scorecard's arithmetic against stamps.

    Parameters
    ----------
    review:
        The typed scorecard (canonical ``_review.json`` payload or the
        legacy-adapter bridge of a prose triple).
    rubric_total:
        The stamped point pool (``_meta.json.rubric_total``, issue #346),
        or ``None`` for a legacy unstamped review (degrades the
        weights-sum check to an info-level ``pool_unstamped`` finding).
    advance_threshold:
        The stamped advance threshold (``_meta.json.advance_threshold``),
        or ``None`` for a legacy unstamped review (skips the
        total-vs-threshold leg of the advance check; the critical-flag
        leg still runs).
    weight_adjustments:
        Sparse ``dim_N -> int delta`` dict when an artifact-type overlay
        applies (``_summary.md.rubric_overlay.weight_adjustments``,
        memo-review step 4i). The effective pool is ``rubric_total`` +
        the sum of deltas (e.g. memo's vision-document overlay: 44 - 6 =
        38). ``None`` / empty means the base pool applies.
    advance:
        The declared advance decision from prose (``verdict.md``'s
        ``Decision: advance: true|false``), when the caller has it. When
        ``None``, the check falls back to ``review.verdict == ADVANCE``.

    Returns the (possibly empty) list of findings. A well-formed
    scorecard returns ``[]`` — zero findings, byte-identical downstream
    behavior.
    """
    findings: List[ScorecardFinding] = []
    scores = review.scores

    # --- Check: per-dim score is a non-negative integer <= its weight.
    # The pydantic Score model already enforces this for payloads built
    # through validation; the raw re-check here keeps the pure function
    # honest for payloads built via model_construct or future relaxed
    # loaders.
    for s in scores:
        if s.score is None:
            continue
        if (
            not isinstance(s.score, int)
            or isinstance(s.score, bool)
            or s.score < 0
            or s.score > s.max
        ):
            findings.append(
                ScorecardFinding(
                    code=SCORE_OUT_OF_BOUNDS,
                    severity=SEVERITY_ERROR,
                    detail=f"{s.dimension}: {s.score} not in [0, {s.max}]",
                    message=(
                        f"dimension {s.dimension!r}: score {s.score} is not "
                        f"a non-negative integer <= its weight {s.max}."
                    ),
                )
            )

    # --- Check: weights sum == effective pool (stamped rubric_total +
    # overlay deltas). Degrades to info-level pool_unstamped when the
    # #346 stamps are absent (legacy pre-#346 review — no pool of record).
    declared_pool = sum(s.max for s in scores)
    if rubric_total is None:
        findings.append(
            ScorecardFinding(
                code=POOL_UNSTAMPED,
                severity=SEVERITY_INFO,
                detail=f"weights sum {declared_pool}, no rubric_total stamp",
                message=(
                    f"_meta.json lacks the issue-#346 rubric stamps "
                    f"(rubric_total / advance_threshold) — legacy pre-#346 "
                    f"review. The scorecard's per-dimension weights sum to "
                    f"{declared_pool} but there is no pool of record to "
                    f"validate against; the weights-sum check is degraded "
                    f"to info. `anvil:rubric-rebackport --legacy-rubric` "
                    f"can supply the pool at read time."
                ),
            )
        )
    else:
        delta = sum(weight_adjustments.values()) if weight_adjustments else 0
        effective_pool = rubric_total + delta
        if declared_pool != effective_pool:
            overlay_note = (
                f" (stamped rubric_total {rubric_total} + overlay "
                f"weight_adjustments {delta:+d})"
                if delta
                else f" (stamped rubric_total {rubric_total})"
            )
            findings.append(
                ScorecardFinding(
                    code=WEIGHTS_SUM_MISMATCH,
                    severity=SEVERITY_ERROR,
                    detail=f"{declared_pool} != {effective_pool}",
                    message=(
                        f"scorecard per-dimension weights sum to "
                        f"{declared_pool} but the effective rubric pool is "
                        f"{effective_pool}{overlay_note}."
                    ),
                )
            )

    # --- Check: declared total == sum of per-dim scores.
    computed_total = sum(
        s.score
        for s in scores
        if isinstance(s.score, int) and not isinstance(s.score, bool)
    )
    if review.total is not None and review.total != computed_total:
        findings.append(
            ScorecardFinding(
                code=TOTAL_MISMATCH,
                severity=SEVERITY_ERROR,
                detail=f"declared {review.total} != computed {computed_total}",
                message=(
                    f"declared total {review.total} does not equal the sum "
                    f"of per-dimension scores ({computed_total})."
                ),
            )
        )

    # --- Check: advance: true requires total >= threshold AND zero
    # critical flags. Cross-checks the prose decision (when supplied)
    # against the machine-readable fields.
    effective_advance = advance
    if effective_advance is None and review.verdict is not None:
        effective_advance = review.verdict == Verdict.ADVANCE
    if effective_advance:
        flag_count = len(review.critical_flags) + sum(
            1 for s in scores if s.critical
        )
        if flag_count:
            findings.append(
                ScorecardFinding(
                    code=ADVANCE_INCONSISTENT,
                    severity=SEVERITY_ERROR,
                    detail=f"advance true with {flag_count} critical flag(s)",
                    message=(
                        f"verdict declares advance: true but {flag_count} "
                        f"critical flag(s) are set — critical flags "
                        f"short-circuit advance regardless of total."
                    ),
                )
            )
        total_of_record = (
            review.total if review.total is not None else computed_total
        )
        if advance_threshold is not None and total_of_record < advance_threshold:
            findings.append(
                ScorecardFinding(
                    code=ADVANCE_INCONSISTENT,
                    severity=SEVERITY_ERROR,
                    detail=(
                        f"advance true with total {total_of_record} < "
                        f"threshold {advance_threshold}"
                    ),
                    message=(
                        f"verdict declares advance: true but the total "
                        f"{total_of_record} is below the stamped "
                        f"advance_threshold {advance_threshold}."
                    ),
                )
            )

    return findings


# Mirrors critics._extract_ip_uspto_summary_json: pull the first
# ```json ... ``` block out of a JSON-in-markdown _summary.md.
_SUMMARY_JSON_BLOCK = re.compile(r"```json\s*(\{.+?\})\s*```", re.DOTALL)


def _extract_summary_json(text: str) -> dict:
    m = _SUMMARY_JSON_BLOCK.search(text)
    if not m:
        return {}
    try:
        return json.loads(m.group(1))
    except (json.JSONDecodeError, ValueError):
        return {}


def _validation_error_findings(exc: ValidationError) -> List[ScorecardFinding]:
    """Convert a pydantic ValidationError into findings (never crash).

    Per-dimension bounds violations (the ``Score._validate_score_bounds``
    message shape) map to ``score_out_of_bounds``; everything else maps
    to ``parse_error``.
    """
    findings: List[ScorecardFinding] = []
    for err in exc.errors():
        msg = str(err.get("msg", ""))
        # Strip pydantic's "Value error, " prefix for the detail.
        detail = re.sub(r"^Value error,\s*", "", msg)
        if "out of bounds" in msg:
            findings.append(
                ScorecardFinding(
                    code=SCORE_OUT_OF_BOUNDS,
                    severity=SEVERITY_ERROR,
                    detail=detail,
                    message=(
                        f"scorecard failed the per-dimension bounds "
                        f"contract: {detail}"
                    ),
                )
            )
        elif "scores must enumerate every rubric dimension" in msg:
            # Sharpened detail for the empty-scores case (issue #912): the
            # generic pydantic message doesn't point a reviewer at the
            # actual cause, and an empty ``scores`` list is the exact
            # shape a fully-bolded/malformed scoring.md table produces
            # once ``parse_memo_scoring_table`` finds zero rows.
            findings.append(
                ScorecardFinding(
                    code=PARSE_ERROR,
                    severity=SEVERITY_ERROR,
                    detail=detail,
                    message=(
                        "scoring table parsed to zero rows — the "
                        "scorecard could not be built into a typed "
                        "Review. Common cause: markdown emphasis (e.g. "
                        "`**5**`) around a Weight or Score cell breaking "
                        "the row shape; verify scoring.md matches the "
                        "documented `| # | Dimension | Weight | Score | "
                        "Justification |` table shape."
                    ),
                )
            )
        else:
            findings.append(
                ScorecardFinding(
                    code=PARSE_ERROR,
                    severity=SEVERITY_ERROR,
                    detail=detail,
                    message=(
                        f"scorecard could not be parsed into a typed "
                        f"Review: {detail}"
                    ),
                )
            )
    if not findings:
        findings.append(
            ScorecardFinding(
                code=PARSE_ERROR,
                severity=SEVERITY_ERROR,
                detail="unparseable scorecard",
                message=f"scorecard could not be parsed: {exc}",
            )
        )
    return findings


def check_review_dir(
    critic_dir: Path,
    *,
    rubric_total: Optional[int] = None,
    advance_threshold: Optional[int] = None,
    weight_adjustments: Optional[Dict[str, int]] = None,
) -> List[ScorecardFinding]:
    """Filesystem convenience: validate one critic sibling dir.

    Loads the review via ``critics.load_review`` (canonical
    ``_review.json`` or the legacy prose triples), reads the issue-#346
    stamps from ``_meta.json``, reads any overlay-adjusted pool from
    ``_summary.md``'s ``rubric_overlay.weight_adjustments`` block, and
    runs ``check_scorecard``. Explicit keyword arguments override the
    on-disk stamps — the ``rubric-rebackport --legacy-rubric`` path
    supplies the pool for unstamped legacy sidecars this way.

    A scorecard that fails the typed bounds contract produces
    ``score_out_of_bounds`` / ``parse_error`` findings rather than an
    unhandled ``pydantic.ValidationError``.

    This is a **read-only** operation. Read-time consumers MUST treat a
    finding-bearing sidecar's verdict as advisory and MUST NOT mutate
    the sidecar (it is immutable once written).
    """
    critic_dir = Path(critic_dir)

    # Stamps from _meta.json (#346), unless overridden by the caller.
    meta: dict = {}
    meta_path = critic_dir / "_meta.json"
    if meta_path.exists():
        try:
            meta = json.loads(meta_path.read_text())
        except (json.JSONDecodeError, ValueError):
            meta = {}
    if rubric_total is None:
        raw = meta.get("rubric_total")
        rubric_total = raw if isinstance(raw, int) else None
    if advance_threshold is None:
        raw = meta.get("advance_threshold")
        advance_threshold = raw if isinstance(raw, int) else None

    # Overlay-adjusted pool from _summary.md (memo-review step 4i),
    # unless overridden by the caller.
    if weight_adjustments is None:
        summary_path = critic_dir / "_summary.md"
        if summary_path.exists():
            summary = _extract_summary_json(summary_path.read_text())
            overlay = summary.get("rubric_overlay")
            if isinstance(overlay, dict):
                adj = overlay.get("weight_adjustments")
                if isinstance(adj, dict):
                    weight_adjustments = {
                        k: v for k, v in adj.items() if isinstance(v, int)
                    }

    # Prose advance decision (memo legacy shape) — cross-checked against
    # the machine-readable fields by check_scorecard.
    advance: Optional[bool] = None
    verdict_path = critic_dir / "verdict.md"
    if verdict_path.exists():
        advance = parse_memo_verdict_decision(verdict_path.read_text())

    # Load the typed review. Reading legacy prose triples is this
    # function's job, so the adapter's DeprecationWarning is suppressed.
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            review = load_review(critic_dir)
    except ValidationError as exc:
        return _validation_error_findings(exc)

    return check_scorecard(
        review,
        rubric_total=rubric_total,
        advance_threshold=advance_threshold,
        weight_adjustments=weight_adjustments,
        advance=advance,
    )


__all__ = [
    "WEIGHTS_SUM_MISMATCH",
    "SCORE_OUT_OF_BOUNDS",
    "TOTAL_MISMATCH",
    "ADVANCE_INCONSISTENT",
    "POOL_UNSTAMPED",
    "PARSE_ERROR",
    "SEVERITY_ERROR",
    "SEVERITY_INFO",
    "ScorecardFinding",
    "check_scorecard",
    "check_review_dir",
]
