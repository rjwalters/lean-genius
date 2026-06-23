# Problem Selection Report

**Date**: 2026-04-12
**Mode**: SELECT
**Pool Status**: 17 available, 1233 in-progress, 556 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: infinitude-primes-4k1-oq-01
- **Name**: Fermat's theorem on sums of two squares (p ≡ 1 mod 4 ⟺ p = a² + b²)
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 8/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unselected candidates**: Composite = 87 =
   (tractability 8 × 10) + significance 7, tied with erdos-729-oq-02 (also 87).
   erdos-729-oq-02 was rejected because it was already selected twice in previous
   seeker runs (commits e0296b9b, e1d3e85e). This problem has never been selected.

2. **EMPTY knowledge tier**: No research has been done on this problem. Per the
   algorithm, EMPTY-tier problems have highest priority (knowledge_tier=0).

3. **High tractability (8/10)**: Mathlib's `NumberTheory.SumTwoSquares` module is
   already imported by the gallery proof. The infrastructure likely exists — the
   main work is assembling a clean biconditional statement. Well-suited for
   autonomous research.

4. **Diversity maintained**: Last 3 selections were number theory (×2) and geometry.
   Not all same domain — no diversity penalty applies. This problem is number theory
   but adds quadratic-residue/algebraic-number-theory flavor distinct from the
   arithmetic series and p-adic valuation selections.

## Rejection Summary

- **Candidates considered**: 17
- **Candidates rejected**: 16
  - `erdos-729-oq-02` (score 87): rejected — already selected twice in previous runs
  - `erdos-1168-oq-04` (score 77): lower composite score
  - `erdos-166-oq-04` (score 77): lower composite score
  - `erdos-998-oq-02` (score 77): lower composite score
  - `erdos-998-oq-04` (score 77): lower composite score
  - `mean-value-theorem-oq-04` (score 77): already selected (commit 09d5fda2)
  - `abel-ruffini-oq-04-oq-02-oq-02-oq-01` (score 76): lower score
  - `erdos-729-oq-04` (score 76): lower score, same problem family as rejected top
  - Remaining 8 candidates: composite scores 67 or below
- **Confidence**: high — clear score separation (87 vs 77 for runner-up)

## Related Gallery Proofs

- `infinitude-primes-4k1`: Source proof — uses one direction of Fermat's theorem via Euler's criterion
- `fundamental-theorem-arithmetic`: Prime factorization infrastructure
- `pythagorean-theorem`: Sum of squares geometric context

## Suggested First Steps

1. **OBSERVE**: Survey `Mathlib.NumberTheory.SumTwoSquares` — look for `Nat.Prime.sq_add_sq`,
   `Int.sq_add_sq_of_sq_add_sq`, or similar. Check if the biconditional already exists.

2. **ORIENT**: Read `proofs/Proofs/InfinitudePrimes4k1.lean` (already done in selection).
   Map which Mathlib lemmas are used and which could bridge to the full characterization.
   Check `GaussianInt` for the Gaussian integer factorization approach.

3. **DECIDE**: If Mathlib has the forward direction as a theorem, write a clean wrapper.
   If not, determine whether the Gaussian integer path or descent path is more tractable.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 17 |
| In Progress | 1233 |
| Completed | 556 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

Pool has 17 available problems — above the 15-problem threshold. However, the `.lean/state/candidate-pool.json` was found to be stale (showed 19 available, database had only 1 truly available before sync to `research/candidate-pool.json`). The stale pool file at `.lean/state/` should be updated to match the synced database.

- **Pool depth**: adequate (17 available, threshold 15)
- **Recommendation**: Pool healthy. Monitor for claims reducing available count below 15.
- **Next refresh recommended**: When available drops below 12
