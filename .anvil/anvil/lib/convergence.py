"""Convergence/termination primitives for the review/revise loop.

This module is the load-bearing primitive for #27 — *stable-score termination
as secondary stop condition* — and #559 — *NO-GO terminal sink for
thesis-level failure*. It exists alongside ``anvil/lib/critics.py``
(per-iteration aggregation and verdict) and is invoked by an orchestrator or
skill review-command that has access to per-iteration score history.

The functions here are **pure**: no filesystem access, no ``_progress.json``
reads. The caller is responsible for extracting score history from the
canonical ``metadata.score_history`` array documented in
``anvil/lib/snippets/progress.md`` and passing it in.

Resolution order
----------------

When deciding whether to terminate the draft↔review↔revise loop, the
following conditions are evaluated in order — the **first** match wins:

1. ``NO_GO`` (``Verdict.NO_GO``) — a critical flag of type ``"no_go"`` is
   present (issue #559). This is the highest-priority terminator: the
   evaluator has concluded the *thesis itself* fails, not that the prose
   has a defect. NO-GO short-circuits the revise loop (the loop's job is
   no longer "raise the score") and requires an explicit operator
   override to resurrect. NO-GO is resolved BEFORE ``CRITICAL_FLAG``
   because a ``no_go``-typed flag is a stronger signal than a generic
   critical flag.
2. ``CRITICAL_FLAG`` (``Verdict.BLOCK``) — any other *blocking* critical
   flag is set. ``pending_dependency``-typed flags (issue #842) are
   explicitly EXCLUDED here: they are visible-but-non-blocking
   outstanding-dependency markers, never a blocker verdict, and never
   deduct a dimension score. The terminal-state gate (READY / AUDITED)
   for an unresolved pending marker is enforced *separately* by the
   consuming skill via :func:`has_pending_dependency_flag` — decoupled
   from the score/verdict path here, exactly as #842 specifies.
3. ``THRESHOLD_MET`` (``Verdict.ADVANCE``) — latest total meets threshold.
4. ``MAX_ITERATIONS`` (``Verdict.REVISE``) — iteration cap exhausted. The
   verdict remains ``REVISE`` because the work did not converge; the
   orchestrator/human reads ``termination_reason`` to know why the loop
   stopped.
5. ``STALLED`` (``Verdict.STALLED``) — the last ``lookback`` totals are
   all within ``± window`` of each other AND below the threshold. This is
   the lowest-priority terminator: the loop has plateaued but did not
   demonstrably converge or fail a harder check.
6. Otherwise — ``(Verdict.REVISE, "")``: no termination, the loop
   continues.

Defaults match the rationale in #27: ``window=1``, ``lookback=2`` — two
consecutive rounds within ±1 trigger ``STALLED``.

NO-GO discrimination (issue #559)
---------------------------------

``decide_termination`` accepts critical-flag information in two equivalent
shapes for backwards compatibility:

- ``any_critical: bool`` (legacy, pre-#559) — the caller has already
  resolved whether any critical flag is set. The NO-GO branch cannot fire
  via this shape (no per-flag-type discrimination is possible); legacy
  callers route through ``CRITICAL_FLAG`` exactly as before.
- ``critical_flags: list[str | CriticalFlag]`` (new, #559) — the caller
  passes the full list of critical flags. The NO-GO branch fires when any
  entry has ``type == "no_go"``. Other types route through
  ``CRITICAL_FLAG`` exactly as before.

Both shapes are accepted via separate keyword arguments; exactly one
should be set per call (the legacy ``any_critical`` bool is honored when
``critical_flags`` is None for byte-identical backwards-compat with all
pre-#559 callers).

This file's behavior is mirrored in the markdown convention layer at
``anvil/lib/snippets/rubric.md`` ("Convergence logic") and
``anvil/lib/snippets/state_machine.md`` ("Convergence and iteration cap").
The Python implementation here is the source of truth for programmatic use;
the snippets are the source of truth for LLM-side authoring. They MUST agree.
"""

from __future__ import annotations

from typing import List, Optional, Tuple, Union

from anvil.lib.review_schema import CriticalFlag, Verdict


# Canonical termination_reason values. These match the optional top-level
# ``termination_reason`` field documented in ``anvil/lib/snippets/progress.md``.
TERMINATION_THRESHOLD_MET = "THRESHOLD_MET"
TERMINATION_CRITICAL_FLAG = "CRITICAL_FLAG"
TERMINATION_STALLED = "STALLED"
TERMINATION_MAX_ITERATIONS = "MAX_ITERATIONS"
TERMINATION_NO_GO = "NO_GO"

# The skill-defined critical-flag type that triggers NO-GO. Skill-local
# (memo today; other skills opt in per the #559 brief). Documented at
# ``anvil/lib/snippets/state_machine.md`` §"Terminal verdict: NO-GO".
NO_GO_FLAG_TYPE = "no_go"

# The additive critical-flag type for an outstanding pending-measurement
# dependency (issue #842). Modeled on ``NO_GO_FLAG_TYPE``'s discipline —
# additive, no schema-version bump — but with the OPPOSITE verdict
# posture: where a ``no_go`` flag is a *stronger* terminator than a
# generic critical flag (short-circuiting to ``NO_GO``), a
# ``pending_dependency`` flag is a *weaker* signal than a generic
# critical flag — it must **never** force ``Verdict.BLOCK`` and must
# **never** deduct a dimension score. It surfaces in
# ``AggregatedReview.critical_flags`` purely for visibility ("an
# honestly-declared value is still outstanding"), while the terminal-
# state gate (READY / AUDITED) is enforced *separately* by the consuming
# skill via :func:`has_pending_dependency_flag` (or a deterministic
# re-run of ``anvil/lib/pending_marker.py``). See that module and
# ``anvil/lib/snippets/pending_marker.md`` for the full convention.
PENDING_DEPENDENCY_FLAG_TYPE = "pending_dependency"


def _flag_type(cf: Union[str, CriticalFlag]) -> Optional[str]:
    """Return the ``type`` tag of a flag given either shape, else ``None``."""
    if isinstance(cf, CriticalFlag):
        return cf.type
    if isinstance(cf, str):
        return cf
    return None


def _has_no_go_flag(
    critical_flags: Optional[List[Union[str, CriticalFlag]]],
) -> bool:
    """Return True when ``critical_flags`` contains a ``no_go``-typed entry.

    Accepts either ``CriticalFlag`` instances or bare ``str`` type-tags so
    callers can pass the lighter shape when constructing flags is overkill
    (tests, fast paths).
    """
    if not critical_flags:
        return False
    return any(_flag_type(cf) == NO_GO_FLAG_TYPE for cf in critical_flags)


def has_pending_dependency_flag(
    critical_flags: Optional[List[Union[str, CriticalFlag]]],
) -> bool:
    """Return True when ``critical_flags`` contains a ``pending_dependency`` entry.

    The public query for the **terminal-state gate** (issue #842): a
    consuming skill (paper first) calls this before promoting a thread to
    a terminal state (READY / AUDITED) — independently of the score /
    ordinary-critical-flag verdict path — so an artifact can never reach a
    terminal state with an unresolved ``[PENDING <source>]`` marker still
    in its body. Accepts either ``CriticalFlag`` instances or bare ``str``
    type-tags (same lenient shape as :func:`_has_no_go_flag`).
    """
    if not critical_flags:
        return False
    return any(
        _flag_type(cf) == PENDING_DEPENDENCY_FLAG_TYPE for cf in critical_flags
    )


def blocking_critical_flags(
    critical_flags: Optional[List[Union[str, CriticalFlag]]],
) -> List[Union[str, CriticalFlag]]:
    """Filter ``critical_flags`` down to the ones that force ``Verdict.BLOCK``.

    Excludes ``pending_dependency``-typed flags (issue #842): those are
    visible-but-non-blocking outstanding-dependency markers, never a
    blocker verdict. A ``no_go``-typed flag IS retained here (it is a
    blocker, resolved to the stronger ``NO_GO`` verdict upstream). Used by
    ``anvil/lib/critics.py`` to compute ``any_critical`` without letting a
    pending-only review force BLOCK.
    """
    if not critical_flags:
        return []
    return [
        cf
        for cf in critical_flags
        if _flag_type(cf) != PENDING_DEPENDENCY_FLAG_TYPE
    ]


def check_stable(
    history: List[Optional[int]],
    window: int = 1,
    lookback: int = 2,
) -> bool:
    """Return True when the last ``lookback`` totals are all within ``± window``.

    A "stable" history means successive revisions have stopped improving:
    the aggregated total bounces inside a small window without crossing the
    threshold. This is the input to the ``STALLED`` termination branch.

    Parameters
    ----------
    history:
        Per-iteration aggregated totals in iteration order. ``None`` entries
        represent iterations where no scorecard was produced (e.g., a
        critical-flag short-circuit occurred before scoring). ``None`` in the
        relevant window prevents a stability decision and returns ``False``.
    window:
        Allowed spread (max - min) across the last ``lookback`` totals.
        Default ``1`` (two consecutive rounds within ±1).
    lookback:
        Number of trailing entries to examine. Default ``2`` (compare the
        last two rounds).

    Returns
    -------
    bool
        ``True`` when (1) there are at least ``lookback`` entries, (2) none of
        the last ``lookback`` entries are ``None``, and (3) the max-minus-min
        spread of the last ``lookback`` entries is ``<= window``. Otherwise
        ``False``.
    """
    if lookback < 2:
        # A single-entry "stability" check is meaningless. The contract is
        # that stability requires comparison across at least two entries.
        return False
    if len(history) < lookback:
        return False
    tail = history[-lookback:]
    if any(x is None for x in tail):
        return False
    # mypy/pyright: after the None check, all entries are int.
    ints: List[int] = [int(x) for x in tail]  # type: ignore[arg-type]
    return (max(ints) - min(ints)) <= window


def decide_termination(
    history: List[Optional[int]],
    threshold: int,
    any_critical: bool = False,
    iteration: int = 0,
    max_iterations: int = 0,
    window: int = 1,
    lookback: int = 2,
    *,
    critical_flags: Optional[List[Union[str, CriticalFlag]]] = None,
) -> Tuple[Verdict, str]:
    """Decide the next-step verdict + termination_reason for the loop.

    Resolution order (first match wins):

    1. ``no_go`` critical-flag present -> ``(NO_GO, "NO_GO")`` — issue #559.
       Fires only when ``critical_flags`` is provided and contains a
       ``CriticalFlag(type="no_go", ...)`` (or the bare-string sentinel
       ``"no_go"``). The legacy ``any_critical`` bool path NEVER triggers
       NO-GO — callers that have not migrated to the typed list continue
       to route through ``CRITICAL_FLAG`` exactly as before.
    2. ``any_critical`` (or any non-``no_go`` critical flag in
       ``critical_flags``) -> ``(BLOCK, "CRITICAL_FLAG")``
    3. ``history[-1] >= threshold`` -> ``(ADVANCE, "THRESHOLD_MET")``
    4. ``iteration >= max_iterations`` -> ``(REVISE, "MAX_ITERATIONS")``.
       The verdict stays ``REVISE`` (not ``STALLED``) because hitting the cap
       is a different signal from a demonstrated plateau: the work simply ran
       out of budget. The orchestrator/human reads ``termination_reason`` to
       distinguish the two.
    5. ``check_stable(history, window, lookback)`` -> ``(STALLED, "STALLED")``
    6. Else -> ``(REVISE, "")`` — loop continues, no termination yet.

    Parameters
    ----------
    history:
        Per-iteration aggregated totals in iteration order. ``None`` entries
        are allowed (see ``check_stable``). Pass ``[]`` if no scorecard is
        available yet; the threshold check requires at least one entry.
    threshold:
        The advance threshold for this rubric.
    any_critical:
        Whether the latest review surfaced any critical flag. Legacy
        pre-#559 shape; cannot trigger NO-GO on its own. When
        ``critical_flags`` is also passed, ``any_critical`` is derived from
        it (``bool(critical_flags)``) and the explicit kwarg is ignored.
    iteration:
        Current iteration number (1-indexed). The iteration that just
        produced ``history[-1]``.
    max_iterations:
        Iteration cap from ``<thread>/.anvil.json`` (default ``4``).
    window:
        Stability window. Default ``1``.
    lookback:
        Number of trailing entries to examine for stability. Default ``2``.
    critical_flags:
        Optional new-shape (post-#559) list of critical flags as either
        ``CriticalFlag`` instances or bare ``str`` type-tags. When provided,
        ``decide_termination`` discriminates ``no_go`` from other types and
        can return ``(NO_GO, "NO_GO")``. When ``None`` (default), the
        legacy ``any_critical`` bool path applies and NO-GO is unreachable.

    Returns
    -------
    tuple[Verdict, str]
        The decided verdict and termination_reason. ``termination_reason``
        is the empty string when the loop should continue (no termination).
    """
    # The typed list (post-#559) is the canonical critical-flag input for
    # NO-GO discrimination. The legacy ``any_critical`` bool remains a
    # truthful generic-critical signal — it may be True even when
    # ``critical_flags`` is empty (per-dimension ``Score.critical`` rolls up
    # into ``any_critical`` without producing a top-level ``CriticalFlag``).
    # The composite contract is: NO-GO fires only from the typed list;
    # generic CRITICAL_FLAG fires from EITHER the typed list OR the bool.
    #
    # ``pending_dependency``-typed flags (issue #842) are excluded from the
    # generic-critical trigger: they are visible-but-non-blocking
    # outstanding-dependency markers and must NEVER force ``Verdict.BLOCK``.
    # The terminal-state gate is enforced separately by the consuming skill
    # via :func:`has_pending_dependency_flag`.
    derived_any_critical = (
        bool(blocking_critical_flags(critical_flags)) or bool(any_critical)
    )

    # 1. NO-GO short-circuits everything (issue #559). Highest priority:
    #    the evaluator has concluded the thesis itself fails. Only fires
    #    when the typed list is provided AND contains a no_go-typed flag.
    if _has_no_go_flag(critical_flags):
        return (Verdict.NO_GO, TERMINATION_NO_GO)

    # 2. Generic critical flag — every other critical-flag type.
    if derived_any_critical:
        return (Verdict.BLOCK, TERMINATION_CRITICAL_FLAG)

    # 3. Threshold met — convergence achieved.
    if history and history[-1] is not None and history[-1] >= threshold:
        return (Verdict.ADVANCE, TERMINATION_THRESHOLD_MET)

    # 4. Iteration cap exhausted. Verdict stays REVISE (the work did not
    #    converge); the termination_reason is MAX_ITERATIONS.
    if iteration >= max_iterations:
        return (Verdict.REVISE, TERMINATION_MAX_ITERATIONS)

    # 5. Demonstrated plateau — score stable across the last `lookback` rounds.
    if check_stable(history, window=window, lookback=lookback):
        return (Verdict.STALLED, TERMINATION_STALLED)

    # 6. No termination — loop continues.
    return (Verdict.REVISE, "")


__all__ = [
    "TERMINATION_THRESHOLD_MET",
    "TERMINATION_CRITICAL_FLAG",
    "TERMINATION_STALLED",
    "TERMINATION_MAX_ITERATIONS",
    "TERMINATION_NO_GO",
    "NO_GO_FLAG_TYPE",
    "PENDING_DEPENDENCY_FLAG_TYPE",
    "has_pending_dependency_flag",
    "blocking_critical_flags",
    "check_stable",
    "decide_termination",
]
