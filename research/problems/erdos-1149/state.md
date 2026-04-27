# Current State

**Phase**: ACT (axiom-elimination opportunity)
**Since**: 2026-04-27
**Iteration**: 3

## Current Focus

Eliminating the `random_coprime_density` axiom. The Bergelson–Richter axiom is left in place as a deep ergodic-theory result not currently in Mathlib's reach.

## Active Approach

Möbius inversion + Tannery's theorem on the partial sums:

1. Counting identity: `countCoprimePairs N = ∑_{d=1}^N μ(d) ⌊N/d⌋²`.
2. Asymptotic interchange: `(1/N²) ∑_{d=1}^N μ(d) ⌊N/d⌋² → ∑_d μ(d)/d²`.
3. Closed form: `∑_d μ(d)/d² = 1/ζ(2) = 6/π²` via Mathlib's `hasSum_zeta_two` and `moebius_mul_coe_zeta`.

All three steps stay within Mathlib's toolkit; no external theory needed.

## Blockers

- None hard. Step B (Möbius–Tannery interchange) is the analytic crux; expect ~80–120 lines.

## Next Action

Implement Step A (counting identity) as a standalone lemma `countCoprimePairs_eq_moebius_sum`, generalizing `pairs_with_common_factor` from prime p to arbitrary d ≥ 1.

## Attempt Counts

- Total attempts: 0 (axiom-elimination not yet attempted)
- Current approach attempts: 0
- Approaches tried: 0
