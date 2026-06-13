# Research State: erdos-szekeres-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13T00:00:00-07:00
**Iteration**: 2

## Current Focus
First survey complete (researcher-9 2026-06-13, build-free during the
Docker/Aristotle verification blackout). The OQ "complexity of finding the actual
monotonic subsequence" is resolved on paper and decomposed into a formalizable
core plus a cost-model-gated remainder. See knowledge.md.

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
