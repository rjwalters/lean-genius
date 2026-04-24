# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT (pool at threshold)
**Pool Status**: 15 available (at minimum threshold of 15), 558 in-progress, 1419 completed

## Selected Problem

- **ID**: derangements-convergence-oq-03
- **Name**: Prove D(n) = round(n!/e) Integer Identity for Derangements
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 8/10
- **Knowledge Score**: EMPTY (no prior workspace)
- **Status**: in-progress → promoted to available

## Selection Rationale

1. **EMPTY knowledge tier** — highest priority (composite score = 87 vs WEAK at -924 or below)
2. **High tractability (8)** — all mathematical ingredients exist in `DerangementsOQ03.lean`; main work is Lean API
3. **Domain diversity** — combinatorics/rounding, distinct from recent geometry (ptolemys, triangle) and analysis (erdos-512, erdos-268)
4. **No active lock** — problem is free, last workspace modification >3 days ago
5. **Clear first step** — import `DerangementsOQ03.derangements_convergence_rate` and search Mathlib for `Nat.round`

## Rejection Summary

- **Candidates considered**: 15 available (WEAK) + 6 top in-progress (EMPTY)
- **Rejected WEAK available**: All 15 available problems have WEAK knowledge (4-5 items); composite ≈ -924 to -963 — below any EMPTY candidate
- **Rejected EMPTY in-progress**:
  - `solution-of-cubic-oq-03-oq-04` (composite 78): loses on tractability (7 vs 8)
  - `sylow-theorem-oq-04` (composite 77): loses on both tractability and significance
- **Confidence**: High — clear gap between EMPTY tier (87) and WEAK tier (-924)

## Related Gallery Proofs

- `derangements-convergence`: Main convergence result — D(n)/n! → 1/e
- `derangements-oq-03`: Sharp error bound |D(n)/n! - 1/e| ≤ 1/(n+1)! — FULLY PROVED, key ingredient
- `derangements-convergence-oq-01`: k-fixed-point Poisson convergence, uses derangements rate as sorry

## Suggested First Steps

1. **OBSERVE**: Search Mathlib for `Nat.round`, `Real.round`, `Int.round` — determine which type to use
2. **ORIENT**: Import `Proofs.DerangementsOQ03` and verify `derangements_convergence_rate` accessible
3. **DECIDE**: Choose formulation — `Nat.round (n! / e)` or equivalent floor-based statement
4. **ACT**: Write `derangements_round` using the OQ03 bound multiplied by n!, showing `|(D(n) : ℝ) - n!/e| < 1/2` for n ≥ 2

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 16 (derangements-convergence-oq-03 promoted) |
| In Progress | 557 |
| Completed | 1419 |
| Graduated | 9 |
| Blocked | 3 |

## Candidate Pool Health

Pool was at minimum threshold (15). This selection restores buffer to 16.
All remaining available problems have WEAK knowledge — researchers should pick them up.

- **Pool depth**: Low but restored
- **Recommendation**: Next cycle check if pool dropped; if so, promote `solution-of-cubic-oq-03-oq-04`
- **Next refresh recommended**: 30 minutes
