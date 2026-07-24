# S3 ACT — Unconditional Cauchy estimate μ(r) ≤ M(r) (Part 12)

**Date**: 2026-07-24
**Researcher**: researcher-2
**Branch**: `research/erdos-227-wip01-cauchy-estimate-bridge`
**Build**: host `lake env lean` clean; Docker verification run before PR.

## What landed

The state.md route-1 target: the **HasFPowerSeriesOnBall bridge** giving the
unconditional Cauchy estimate. Part 11's `μ(r) ≤ M(r)` needed non-negative
real coefficients (elementary argument). Part 12 (new, ~200 LOC) removes the
coefficient hypothesis entirely:

* `seriesSum f := (ofScalars ℂ f.coeff).sum`, with `seriesSum_apply`
  identifying it with the naive `∑' n, aₙ zⁿ`.
* `ofScalars_radius_eq_top` — `IsEntire` ⇒ radius = ⊤, via
  `ENNReal.eq_top_of_forall_nnreal_le` + `le_radius_of_summable` +
  `ofScalars_norm` (ℂ is `NormOneClass`).
* `hasFPowerSeriesOnBall_seriesSum`, `differentiable_seriesSum`.
* `norm_coeff_mul_pow_le_maxModulus` — **Cauchy's estimate** `‖aₙ‖rⁿ ≤ M(r)`
  for `r > 0`: uniqueness (`HasFPowerSeriesAt.eq_formalMultilinearSeries`,
  one-dimensional 𝕜 = ℂ) identifies `ofScalars ℂ f.coeff` with
  `cauchyPowerSeries (seriesSum f) 0 R`; `norm_cauchyPowerSeries_le` bounds
  `‖aₙ‖ ≤ ((2π)⁻¹ ∫₀^{2π} ‖f(circleMap 0 r θ)‖) · r⁻ⁿ`; the circle average
  is ≤ M(r) by `intervalIntegral.integral_mono_on` (integrand continuous:
  `Differentiable.continuous.comp continuous_circleMap`).
* `maxTerm_le_maxModulus` — unconditional, `0 ≤ r` (at `r = 0` both sides are
  `‖a₀‖`; `tsum_eq_single 0` collapses the series).
* `termModulusRatio_le_one`, `limit_mem_Icc` — unconditional `L ∈ [0,1]`
  bracket; Part-11 `_of_nonneg` versions are now special cases.

0 new axioms, 0 new sorries. File: 431 → ~640 lines. The 3 deep axioms
(Clunie / Clunie–Hayman) and the 1 sorry (`positive_coeffs_normal`,
Wiman–Valiron) are untouched — still "materially new mechanism required".

## Mathlib API notes (v4.31)

* `FormalMultilinearSeries.ofScalars E c` (E explicit), `ofScalars_norm`
  needs `[NormOneClass E]`; `coeff_ofScalars`; `ofScalars_sum_eq` states
  `ofScalarsSum c x = ∑' n, c n • x ^ n` — unfold `ofScalarsSum` to reach
  `(ofScalars E c).sum`.
* `ENNReal.top_pos` is GONE — use `simp` (or `zero_lt_top`).
* `le_radius_of_summable` lives in `Analysis/Analytic/ConvergenceRadius.lean`.
* `cauchyPowerSeries` + `norm_cauchyPowerSeries_le` live in
  `MeasureTheory/Integral/CircleIntegral.lean`; `circleMap` in
  `Analysis/SpecialFunctions/Complex/CircleMap.lean`
  (`circleMap 0 R θ = R * exp (θ * I)` — note `θ * I`, not `I * θ`;
  bridge with `mul_comm`).
* `Differentiable.hasFPowerSeriesOnBall` takes `R : ℝ≥0`, yields radius `∞`;
  build `R := ⟨r, hr.le⟩` and `(R : ℝ) = r` is `rfl`.
* `gcongr` auto-discharges nonneg side conditions — a following bullet
  `exact ...` then errors "No goals to be solved"; don't pre-supply them.

## Next

Remaining routes unchanged from state.md: the sorry and 3 axioms need
Clunie/Clunie–Hayman/Wiman–Valiron theory absent from Mathlib (DEEP).
The elementary + bridge layers are now both saturated. Plausible future
increments: relate `maxModulus` to `sSup` over the closed ball via the
maximum principle (Mathlib `Complex.AbsMax`), or an `AnalyticAt`-based
restatement of `IsEntire`.
