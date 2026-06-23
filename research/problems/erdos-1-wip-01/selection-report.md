# Problem Selection Report

**Date**: 2026-04-25
**Mode**: SELECT
**Pool Status**: 23 available, 556 in-progress, 1427 completed, 8 graduated, 4 blocked

## Selected Problem

- **ID**: `erdos-1-wip-01`
- **Name**: Complete Erdős Problem #1 — Distinct Subset Sums (WIP Extension)
- **Tier**: A
- **Significance**: 9/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 items (EMPTY)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier** (0 items): highest priority tier — no research has been done
   on this problem yet. All 19 EMPTY-tier problems rank above MODERATE and RICH.
2. **Highest composite score**: sig=9, tract=6 → composite = 0 + 60 + 9 = **69**
   (next best: `szemeredi-regularity-oq-02` scores 68).
3. **Domain diversity**: Previous selection was `cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01`
   (linear algebra). Erdős #1 is additive combinatorics/number theory — different domain.
4. **Tractability justified**: Main conjecture is open, but intermediate goals (entropy
   bound formalization, DFX lemma framework) are achievable.
5. **Gallery foundation exists**: `erdos-1` parent proof has 0 sorries — solid base.

## Rejection Summary

- **Candidates considered**: 23 available
- **Claimed (skipped)**: `lebesgue-measure-oq-06`, `erdos-476-oq-05-wip-01`, `dissection-of-cubes-oq-04`
  (all RICH tier but have active .lock claims)
- **Lower priority** (MODERATE, 12 items): `cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01`
- **Lower score**: All other EMPTY-tier problems score ≤ 68 (lower sig or tractability)
- **Confidence**: high — clear score separation (69 vs 68 for runner-up)

## Related Gallery Proofs

- `erdos-1`: Parent — counting bound N ≥ (2^n-1)/n and max element bound (fully proved)
- `erdos-1-oq-01`: Extension question on optimality of the bound
- `erdos-1-oq-02`: Generalization directions
- `erdos-1-oq-03`: Alternative proof approaches
- `erdos-1-oq-04`: Connection to other combinatorial problems

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/Erdos1Problem.lean` — understand existing formalization
   and identify extension hooks.
2. **ORIENT (Scout)**: Survey Mathlib for entropy API (`measureEntropy`, information theory
   in `Mathlib.MeasureTheory.Measure.MeasureSpace`) and additive combinatorics tools.
3. **DECIDE**: Choose between:
   - Formalizing DFX entropy argument (challenging, high value)
   - Adding structural lemmas (extremal set properties, connection to Sidon sets)
   - Axiomatizing the main conjecture with formal statement (practical, lower value)

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 23 |
| In Progress | 556 |
| Completed | 1427 |
| Graduated | 8 |
| Skipped | 0 |
| Blocked | 4 |

## Candidate Pool Health

Pool is **adequate** (23 available, 8 above threshold of 15).

- Pool depth: adequate
- 19 EMPTY problems → rich unexplored territory for researchers
- 18 active researcher claims → high activity level
- Recommendation: Pool healthy, no replenishment needed
- Next refresh recommended: ~30 minutes (next seeker cycle)
