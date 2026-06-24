import Mathlib

/-!
# Geometric Series OQ-01 / OQ-01 / OQ-02: Abel Summation of `1 − 2 + 3 − 4 + ⋯ = 1/4`

A sibling of `GeometricSeriesOQ01OQ01OQ01` (which formalizes Frobenius's theorem), both
children of `GeometricSeriesOQ01OQ01` (*Abel Summability of Grandi's Series* = `1/2`).  This
entry treats the **term-by-term derivative** of Grandi's series, Euler's divergent series
`1 − 2 + 3 − 4 + ⋯`, and proves it is **Abel summable to `1/4`**.

## What this file proves

Differentiating the geometric series gives, for `|x| < 1`, the closed form
`∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/(1+x)²` (the ratio `−x` form of `∑ (n+1) yⁿ = 1/(1−y)²`).  Its
**Abel limit** as `x → 1⁻` is the boundary value `1/(1+1)² = 1/4`.

* `hasSum_alt_nat`: `HasSum (fun n => (−1)ⁿ (n+1) xⁿ) (1/(1+x)²)` for `|x| < 1`;
* `alt_nat_power_series`: the `tsum` form `∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/(1+x)²`;
* `abel_tendsto_quarter`: the Abel limit `lim_{x→1⁻} ∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/4`.

This value `1/4` is consistent with the analytic continuation `η(−1) = 1/4` of the Dirichlet
eta function (`η(s) = ∑ (−1)ⁿ⁻¹ n⁻ˢ`), and with `ζ(−1) = −1/12` via `η(s) = (1 − 2¹⁻ˢ) ζ(s)`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace GeometricSeriesOQ01OQ01OQ02

open Filter Topology

/-- **The Abel power series of `1 − 2 + 3 − 4 + ⋯`.** For `|x| < 1`,
    `∑ₙ (−1)ⁿ (n+1) xⁿ` has sum `1/(1+x)²` — the derivative of the geometric series, with
    ratio `−x`. Obtained by adding `∑ n yⁿ = y/(1−y)²` and `∑ yⁿ = 1/(1−y)` at `y = −x`. -/
theorem hasSum_alt_nat {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1) * x ^ n) ((1 + x) ^ 2)⁻¹ := by
  have hy : ‖(-x : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_neg]; exact hx
  have s1 : HasSum (fun n : ℕ => (n : ℝ) * (-x) ^ n) (-x / (1 - -x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hy
  have s2 : HasSum (fun n : ℕ => (-x : ℝ) ^ n) (1 - -x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hy
  have hsum := s1.add s2
  have hx1 : (1 + x) ≠ 0 := by
    have : -1 < x := (abs_lt.mp hx).1
    intro h; nlinarith
  have hfun : (fun n : ℕ => (n : ℝ) * (-x) ^ n + (-x) ^ n)
      = (fun n : ℕ => (-1 : ℝ) ^ n * (n + 1) * x ^ n) := by
    funext n
    rw [neg_pow]
    ring
  have hval : -x / (1 - -x) ^ 2 + (1 - -x)⁻¹ = ((1 + x) ^ 2)⁻¹ := by
    rw [show (1 - -x : ℝ) = 1 + x by ring]
    field_simp
    ring
  rw [hfun, hval] at hsum
  exact hsum

/-- **Closed form** of the `tsum`: `∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/(1+x)²` for `|x| < 1`. -/
theorem alt_nat_power_series {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n = ((1 + x) ^ 2)⁻¹ :=
  (hasSum_alt_nat hx).tsum_eq

/-- **Abel summation of `1 − 2 + 3 − 4 + ⋯ = 1/4`.** The Abel limit of `∑ (−1)ⁿ (n+1) xⁿ` as
    `x → 1⁻` is `1/4`, the boundary value of the closed form `1/(1+x)²`. -/
theorem abel_tendsto_quarter :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n)
      (𝓝[<] 1) (𝓝 (1 / 4)) := by
  have hev : (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n)
      =ᶠ[𝓝[<] 1] fun x => ((1 + x) ^ 2)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num))]
      with x hx1 hx2
    exact alt_nat_power_series (abs_lt.mpr ⟨hx2, hx1⟩)
  rw [tendsto_congr' hev]
  have h : Tendsto (fun x : ℝ => ((1 + x) ^ 2)⁻¹) (𝓝 1) (𝓝 (1 / 4)) := by
    have hbase : Tendsto (fun x : ℝ => (1 + x) ^ 2) (𝓝 1) (𝓝 (((1 : ℝ) + 1) ^ 2)) :=
      (tendsto_const_nhds.add tendsto_id).pow 2
    have hinv := hbase.inv₀ (by norm_num : ((1 : ℝ) + 1) ^ 2 ≠ 0)
    rwa [show (((1 : ℝ) + 1) ^ 2)⁻¹ = 1 / 4 by norm_num] at hinv
  exact h.mono_left nhdsWithin_le_nhds

/-- Euler's series `1 − 2 + 3 − 4 + ⋯` is Abel summable to `1/4`. -/
theorem abel_value_quarter :
    Tendsto (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ n * (n + 1) * x ^ n)
      (𝓝[<] 1) (𝓝 (1 / 4)) := abel_tendsto_quarter

end GeometricSeriesOQ01OQ01OQ02

/-!
## Summary

Abel summation of Euler's divergent series `1 − 2 + 3 − 4 + ⋯`, the term-by-term derivative
of Grandi's series:

- `hasSum_alt_nat` / `alt_nat_power_series`: `∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/(1+x)²` for `|x| < 1`.
- `abel_tendsto_quarter`: `lim_{x→1⁻} ∑'ₙ (−1)ⁿ (n+1) xⁿ = 1/4`, the boundary value of `1/(1+x)²`.

So `1 − 2 + 3 − 4 + ⋯` is Abel summable to `1/4`, the value Euler assigned it and the one
consistent with `η(−1) = 1/4`. A sibling of the Frobenius-theorem entry `oq-01-oq-01-oq-01`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
