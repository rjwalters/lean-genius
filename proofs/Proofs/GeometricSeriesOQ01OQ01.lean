import Mathlib

/-!
# Geometric Series OQ-01 / OQ-01: Abel Summability of Grandi's Series

## The Open Question

The parent (`GeometricSeriesOQ01`, the geometric series at the boundary `|r| = 1`) asks:

> Can **Abel summability** of Grandi's series `1 − 1 + 1 − 1 + ⋯` be formalized? Abel summation
> assigns `lim_{x→1⁻} ∑_{n=0}^∞ (−1)ⁿ xⁿ = lim_{x→1⁻} 1/(1+x) = 1/2`, an independent
> confirmation of the Cesàro value `1/2`.

## What this file proves

* `grandi_power_series`: for `|x| < 1`, the Abel power series sums to the closed form
  `∑'ₙ (−1)ⁿ xⁿ = 1/(1+x)` (the geometric series with ratio `−x`);
* `grandi_abel_tendsto`: the **Abel limit** `lim_{x→1⁻} ∑'ₙ (−1)ⁿ xⁿ = 1/2`, the boundary value
  of `1/(1+x)`.

So Grandi's series is Abel summable to `1/2`, matching its Cesàro value — Abel's method and
Cesàro's method agree here, as Frobenius's theorem guarantees in general.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace GeometricSeriesOQ01OQ01

open Filter Topology

/-- **The Abel power series of Grandi's series.** For `|x| < 1`,
    `∑'ₙ (−1)ⁿ xⁿ = 1/(1+x)` — the geometric series with ratio `−x`. -/
theorem grandi_power_series {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n = (1 + x)⁻¹ := by
  have hnorm : ‖(-x : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_neg]
  have hgeo : ∑' n : ℕ, (-x : ℝ) ^ n = (1 - -x)⁻¹ := tsum_geometric_of_norm_lt_one hnorm
  rw [show (1 - -x : ℝ) = 1 + x by ring] at hgeo
  rw [← hgeo]
  exact tsum_congr fun n => (neg_pow x n).symm

/-- **Abel summability of Grandi's series.** The Abel limit of `∑ (−1)ⁿ xⁿ` as `x → 1⁻` is `1/2`,
    the boundary value of the closed form `1/(1+x)`. -/
theorem grandi_abel_tendsto :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n)
      (𝓝[<] 1) (𝓝 (1 / 2)) := by
  -- on a left-neighborhood of 1, the series equals 1/(1+x)
  have hev : (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n) =ᶠ[𝓝[<] 1] fun x => (1 + x)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num))]
      with x hx1 hx2
    exact grandi_power_series (abs_lt.mpr ⟨hx2, hx1⟩)
  rw [tendsto_congr' hev]
  -- 1/(1+x) → 1/(1+1) = 1/2 by continuity
  have h2 : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝 1) (𝓝 (1 / 2)) := by
    have hnum : Tendsto (fun x : ℝ => 1 + x) (𝓝 1) (𝓝 (1 + 1)) :=
      tendsto_const_nhds.add tendsto_id
    have hinv := hnum.inv₀ (by norm_num : (1 : ℝ) + 1 ≠ 0)
    rwa [show ((1 : ℝ) + 1)⁻¹ = 1 / 2 by norm_num] at hinv
  exact h2.mono_left nhdsWithin_le_nhds

/-- Grandi's series is Abel summable to `1/2`, matching its Cesàro value. -/
theorem grandi_abel_value : Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ n) (𝓝[<] 1)
    (𝓝 (1 / 2)) := grandi_abel_tendsto

end GeometricSeriesOQ01OQ01

/-!
## Summary

Abel summability of Grandi's series, an independent confirmation of its Cesàro value:

- `grandi_power_series`: `∑'ₙ (−1)ⁿ xⁿ = 1/(1+x)` for `|x| < 1` (geometric series, ratio `−x`).
- `grandi_abel_tendsto`: `lim_{x→1⁻} ∑'ₙ (−1)ⁿ xⁿ = 1/2`, the boundary value of `1/(1+x)`.

So `1 − 1 + 1 − 1 + ⋯` is Abel summable to `1/2`, agreeing with its Cesàro sum (Frobenius's
theorem: Cesàro summability implies Abel summability to the same value).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
