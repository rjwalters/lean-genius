# Power Mean Limit: lim_{r→0} M_r = GM

**Problem ID**: amgm-inequality-oq-03-oq-02
**Status**: COMPLETED
**File**: `proofs/Proofs/PowerMeanLimitOQ.lean`

## Summary

Proved that the weighted power mean M_r(z,w) = (sum w_i z_i^r)^(1/r) converges
to the weighted geometric mean GM(z,w) = prod z_i^{w_i} as r -> 0.

10 theorems, 0 sorries, 0 axioms. Fully verified via Docker build (Lean 4.26.0).

## Session 2026-03-05 (Session 1) - Mathlib Compatibility Fix

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Fixed 4 Mathlib API compatibility issues in PowerMeanLimitOQ.lean for Lean 4.26.0
- Fixed `slope`/`vsub` simplification: `vsub_zero` -> `vsub_eq_sub` + `ring`
- Fixed `HasDerivAt.const_mul` argument order: now produces `w * z^r` directly (no rewrite needed)
- Fixed `HasDerivAt.sum` form conversion: `Finset.sum_apply` converts sum-of-functions to function-of-sum
- Fixed `Filter.Tendsto.congr`: use `(Filter.tendsto_congr h_eq).mpr` (iff form) with explicit `(r : ℝ)` annotation
- Cleaned up all unused variable warnings with `_` prefix

### Key Findings
- `HasDerivAt.const_mul (w i)` in current Mathlib already produces `fun y => w * z^y` (correct order)
- `HasDerivAt.sum` returns `HasDerivAt (sum i, f_i)` not `HasDerivAt (fun r => sum i, f_i r)` — use `Finset.sum_apply` to convert
- `slope` now uses `vsub_eq_sub` instead of `vsub_zero` for subtraction
- `Filter.tendsto_congr` (iff version) is more flexible than `Filter.Tendsto.congr` for rewriting

### Files Modified
- `proofs/Proofs/PowerMeanLimitOQ.lean`

### Proof Architecture
1. `sum_weighted_rpow_pos` — positivity of weighted sum
2. `hasDerivAt_sum_weighted_rpow_zero` — derivative of sum at r=0
3. `log_sum_weighted_rpow_zero` — f(0) = 0
4. `hasDerivAt_log_sum_weighted_rpow` — chain rule for log(sum)
5. `tendsto_log_sum_div_rpow` — f(r)/r -> f'(0) via derivative definition
6. `geomMean_eq_exp_sum_log` — GM = exp(sum w_i log z_i)
7. `powerMean_one_eq_arithMean` — M_1 = AM
8. `powerMean_eq_exp_log` — M_r = exp(log(sum)/r)
9. `tendsto_powerMean_zero` — MAIN: M_r -> GM
10. `powerMean_neg1_le_geomMean_le_arithMean` — HM <= GM <= AM
