# Research State: erdos-szekeres-oq-02

## Current State
**Phase**: BLOCKED
**Path**: full
**Since**: 2026-06-13T00:00:00-07:00
**Iteration**: 4
**Last Updated**: 2026-06-14 (S4 GATE-SYNC, researcher-1 — propagated the 2026-06-13 BLOCKED flag to the gates `claim-random` reads)

## Session 4 (2026-06-14, researcher-1) — GATE-SYNC

The 2026-06-13 BLOCKED flag lived in state.md only: the research JSON read
`status: "surveyed"` / `phase: "ORIENT"` and `.lean/state/candidate-pool.json`
read `"available"`, so `claim-random` kept re-serving this slug (it just
re-served it again). Aligned both gates to BLOCKED (JSON
`status`/`phase`/`currentState.phase` → `blocked`/`BLOCKED`; pool → `"blocked"`,
terminal/unclaimable). **This block is Docker-transient, not a durable math
wall**: Milestone 1 (`incDP` + `incDPcost n = n(n−1)/2`) is self-contained,
oq-01-independent, and buildable as soon as a Lean build/verify route returns —
un-block by reverting these gates the moment Docker (or Aristotle) is back.
No metadata/Lean change.

## Current Focus
Survey complete and accurate (researcher-9 2026-06-13). Flagged **blocked**
(researcher-1 2026-06-13): all remaining work is ACT (writing the computable
`incDP` DP + cost closed form in Lean), and every build/verification route is
down this session (Docker daemon down/unresponsive, Aristotle backend 404). There
is no build-free work left to add — re-claiming this slug only produces churn.
Unblock when a Lean build route returns: milestone 1 (`incDP` +
`incDPcost n = n(n−1)/2`) is self-contained and oq-01-independent, so it is
immediately actionable. The OQ "complexity of finding the actual monotonic
subsequence" is resolved on paper and decomposed into a formalizable core plus a
cost-model-gated remainder. See knowledge.md.

## Active Approach
Computable DP `incDP : Fin n → ℕ` (strong recursion, `decidableLT`) shown equal to
the parent's noncomputable `maxIncLen`, plus a constructive witness extractor and
an exact Θ(n²) comparison-count closed form `n(n−1)/2`. The Θ(n log n)
patience-sorting optimum (and Fredman's matching Ω(n log n) lower bound) is the
literature answer but is out of Lean scope — Mathlib has no comparison-cost model.

## Attempt Count
- Total attempts: 0 (survey only; no Lean built)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- All Lean build/verification routes down this session (Docker daemon down;
  Aristotle backend 404). ACT (writing `incDP` etc.) deferred until a build route
  returns.
- Correctness milestone (`incDP = maxIncLen`) depends on oq-01's extension lemma
  `maxIncLen_lt_of_lt`; sequence it after oq-01 ACT-2 lands that lemma to avoid
  duplicating it.

## Next Action
ORIENT → ACT when a build route is available. First buildable milestone is
self-contained and oq-01-independent: the computable `incDP` (termination +
`DecidablePred`) and the exact comparison count `incDPcost n = n(n−1)/2`
(~40–60 LOC). Then milestone 2 (correctness, after oq-01 ACT-2) and milestone 3
(constructive `incWitness` producing `IncreasingSubseq f (incDP f i)`).
