# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 36 available (synced from DB), 558 in-progress, 1420 completed

## Selected Problem

- **ID**: area-of-circle-oq-01-oq-03-oq-01-oq-03
- **Name**: Remove change-of-variables axioms: use MeasureTheory.integral_image_eq_integral_abs_deriv_smul
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available
- **Composite Score**: 77 = (0 × 1000) + (7 × 10) + 7

## Selection Rationale

1. **Axiom-elimination with identified Mathlib target**: The Mathlib lemma
   `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` is explicitly
   named as the solution path. This is the same proven-tractable pattern as
   the LP duality synthesis (tract 9/10 → succeeded).

2. **Domain diversity**: Measure theory / real analysis is not represented in the
   current pool, which is heavy on number theory (Goldbach, twin primes, Sophie
   Germain) and algebra (Jordan-Hölder, Abel-Ruffini). This adds a concrete
   analysis problem.

3. **Concrete scope**: Unlike open conjectures or moonshots, this is a well-scoped
   engineering task: wire up an existing Mathlib lemma to replace an axiom. The
   researcher has a clear target and success criterion.

## Rejection Summary

- **Candidates considered**: 14 existing available + 7,379 new gallery problems
- **New candidates from axiom-elimination search**: 365 problems
- **Rejected (moonshot)**: twin-primes-special-oq-01, weak-goldbach-oq-01,
  sophie-germain-oq-01 (significance ≥ 8, tractability 2 → composite 28-29)
- **Rejected (RICH knowledge)**: erdos-512-incomplete-01 (16 items, composite -2942),
  dissection-of-cubes-oq-04 (16 items, composite -2943)
- **Rejected (WEAK knowledge)**: erdos-268-incomplete-01 (4 items, composite -933)
- **Top existing**: cauchy-schwarz-integral-lp-duality-synthesis (98) and
  abel-ruffini-galois-extensions-oq-04 (78) — already selected in prior cycles
- **Confidence**: medium (score spread between top new candidates is small: 77 vs 67)

## Related Gallery Proofs

- `area-of-circle-oq-01-oq-03-oq-01`: Direct source — Arc-Length Reparametrization,
  contains the axioms to eliminate
- `area-of-circle-oq-01`: Isoperimetric inequality — top of the proof chain
- `cauchy-schwarz-integral-lp-duality-synthesis`: Same axiom-elimination pattern

## Suggested First Steps

1. Read `src/data/proofs/area-of-circle-oq-01-oq-03-oq-01/meta.json` to understand
   the current axiom count and what specific axioms need elimination
2. Search Mathlib for `integral_image_eq_integral_abs_deriv_smul` and read its
   signature and hypotheses
3. Check if `ContDiff.hasStrictFDerivAt_of_hasStrictFDerivAt` and
   `Real.hasStrictDerivAt_inv` can close the required sub-goals

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 36 |
| In Progress | 558 |
| Completed | 1420 |
| Surveyed | 1 |
| Blocked | 3 |
| Graduated | 9 |

## Candidate Pool Health

Pool was below threshold (14 < 15) before selection. Syncing `research/candidate-pool.json`
to `.lean/state/candidate-pool.json` revealed the database had 36 available problems
(pool file was stale). After sync and new insertion:

- **Pool depth**: adequate (36 available)
- **Recommendation**: Pool is healthy — no further replenishment needed this cycle
- **Next refresh recommended**: next seeker cycle (~30 minutes)
