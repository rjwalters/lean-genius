/-
  Erdős Problem #1002 — OQ-02: the Cauchy Distribution *Connection*.

  Background.  Erdős #1002 asks whether the weighted fractional sum
      f(α, n) = (1/log n) · Σ_{k≤n} (1/2 − {αk})
  has an asymptotic distribution function.  Kesten (1960) proved the
  *two-parameter* variant converges to a **Cauchy law**; the one-parameter case
  remains open.  The sibling entry `Erdos1002OQ01` records the Cauchy law only
  through its *cumulative distribution function* (CDF)

      cauchyDistribution ρ c = (1/π)·arctan(ρ c) + 1/2,

  proving it is a genuine distribution function (monotone, limits 0 and 1).
  But the CDF is only one half of the story: the object that actually appears in
  Kesten's theorem is the Cauchy **probability density**

      cauchyDensity ρ x = ρ / (π·(1 + (ρ x)²)).

  This file supplies the missing *connection* between the two — the analytic
  content that makes "Cauchy distribution" mean a bona-fide probability law,
  not just an abstract increasing function:

  * `cauchyDistribution_hasDerivAt` — the CDF differentiates to the density:
        d/dc [cauchyDistribution ρ c] = cauchyDensity ρ c.
  * `integral_cauchyDensity` — the Fundamental Theorem of Calculus form: the CDF
    is the running integral of the density,
        ∫ x in a..b, cauchyDensity ρ x = cauchyDistribution ρ b − cauchyDistribution ρ a.
  * `integral_cauchyDensity_univ` — the **normalization** that certifies the
    density is a probability density: for ρ > 0,
        ∫ x, cauchyDensity ρ x = 1
    (total mass one over all of ℝ), obtained from Mathlib's
    `integral_univ_inv_one_add_sq` (∫ (1+x²)⁻¹ = π) via the scaling x ↦ ρx.
  * supporting: `cauchyDensity_pos` (strict positivity for ρ > 0),
    `cauchyDensity_even` (symmetry about the median 0), and
    `cauchyDensity_continuous`.

  Together with the sibling CDF results, this realises the Cauchy law as a true
  probability distribution with density — the precise sense in which Kesten's
  limit, and hence the conjectured limit in #1002, is "Cauchy".

  Self-contained: imports only Mathlib, axiom-free, no `sorry`.
-/

import Mathlib

set_option maxHeartbeats 400000

open Real MeasureTheory
open scoped Real Topology

namespace Erdos1002OQ02

/-- The Cauchy cumulative distribution function with scale `ρ`
(mirrors `Erdos1002OQ01.cauchyDistribution`): `g_ρ(c) = (1/π)·arctan(ρ c) + 1/2`. -/
noncomputable def cauchyDistribution (ρ c : ℝ) : ℝ :=
  1 / π * arctan (ρ * c) + 1 / 2

/-- The Cauchy probability density with scale `ρ`:
`f_ρ(x) = ρ / (π·(1 + (ρ x)²))`. -/
noncomputable def cauchyDensity (ρ x : ℝ) : ℝ :=
  ρ / (π * (1 + (ρ * x) ^ 2))

/-! ## Elementary shape of the density -/

/-- For a positive scale `ρ`, the Cauchy density is strictly positive everywhere. -/
theorem cauchyDensity_pos (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) : 0 < cauchyDensity ρ x := by
  rw [cauchyDensity]
  exact div_pos hρ (mul_pos pi_pos (by positivity))

/-- The Cauchy density is symmetric about its median `0`: `f_ρ(−x) = f_ρ(x)`. -/
theorem cauchyDensity_even (ρ x : ℝ) : cauchyDensity ρ (-x) = cauchyDensity ρ x := by
  simp only [cauchyDensity, mul_neg, neg_sq]

/-- The Cauchy density is continuous. -/
theorem cauchyDensity_continuous (ρ : ℝ) : Continuous (cauchyDensity ρ) := by
  unfold cauchyDensity
  refine continuous_const.div (by fun_prop) (fun x => ?_)
  exact (mul_pos pi_pos (by positivity)).ne'

/-! ## The density–CDF connection -/

/-- **The CDF differentiates to the density.**  This is the precise sense in
which `cauchyDensity ρ` is the density *of* the distribution `cauchyDistribution ρ`. -/
theorem cauchyDistribution_hasDerivAt (ρ c : ℝ) :
    HasDerivAt (cauchyDistribution ρ) (cauchyDensity ρ c) c := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hden : (1 : ℝ) + (ρ * c) ^ 2 ≠ 0 := by positivity
  -- inner linear map `y ↦ ρ y`
  have hin : HasDerivAt (fun y : ℝ => ρ * y) ρ c := by
    simpa using (hasDerivAt_id c).const_mul ρ
  -- chain rule for `arctan (ρ ·)`
  have harc : HasDerivAt (fun y : ℝ => arctan (ρ * y)) ((1 + (ρ * c) ^ 2)⁻¹ * ρ) c :=
    (hasDerivAt_arctan' (ρ * c)).comp c hin
  -- scale by `1/π` and shift by `1/2`
  have h := (harc.const_mul (1 / π)).add_const (1 / 2)
  have hval : (1 / π) * ((1 + (ρ * c) ^ 2)⁻¹ * ρ) = cauchyDensity ρ c := by
    rw [cauchyDensity]; field_simp
  rw [hval] at h
  exact h

/-- **Fundamental Theorem of Calculus form.**  The CDF is the running integral of
the density: `∫_a^b f_ρ = g_ρ(b) − g_ρ(a)`. -/
theorem integral_cauchyDensity (ρ a b : ℝ) :
    ∫ x in a..b, cauchyDensity ρ x = cauchyDistribution ρ b - cauchyDistribution ρ a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => ?_) ?_
  · exact cauchyDistribution_hasDerivAt ρ x
  · exact (cauchyDensity_continuous ρ).intervalIntegrable a b

/-- **Normalization: total mass one.**  For a positive scale, the Cauchy density
integrates to `1` over all of `ℝ`, certifying it is a probability density.

The proof reduces to Mathlib's `integral_univ_inv_one_add_sq` (`∫ (1+x²)⁻¹ = π`)
through the change of variables `x ↦ ρ x`. -/
theorem integral_cauchyDensity_univ (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ x, cauchyDensity ρ x = 1 := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hρ' : ρ ≠ 0 := hρ.ne'
  -- the scaled inner integral, from `∫ (1+y²)⁻¹ = π` and `x ↦ ρ x`
  have hinner : ∫ x : ℝ, (1 + (ρ * x) ^ 2)⁻¹ = ρ⁻¹ * π := by
    have h := Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) ρ
    simpa only [integral_univ_inv_one_add_sq, smul_eq_mul,
      abs_of_pos (inv_pos.mpr hρ)] using h
  -- pull the constant `ρ/π` out of the integral
  have key : ∫ x, cauchyDensity ρ x = (ρ / π) * ∫ x, (1 + (ρ * x) ^ 2)⁻¹ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hd : (1 : ℝ) + (ρ * x) ^ 2 ≠ 0 := by positivity
    rw [cauchyDensity]; field_simp
  rw [key, hinner]
  have : ρ / π * (ρ⁻¹ * π) = (ρ * ρ⁻¹) * (π / π) := by ring
  rw [this, mul_inv_cancel₀ hρ', div_self hπ, mul_one]

end Erdos1002OQ02
