/-
# Area of Circle OQ-05-OQ-01-Incomplete-01: Completing the Polar-Coordinate Proof for the Scaled Gaussian

**Open Question**: The parent file `AreaOfCircleOQ05OQ01` formalizes the classical
polar-coordinate proof that (∫ e^{-x²} dx)² = π, but only for the *unit* Gaussian
(coefficient a = 1). The scaled Gaussian ∫ e^{-a x²} dx = √(π/a) is proved elsewhere
in the gallery only by invoking Mathlib's `integral_gaussian` black box. Can the
*explicit* polar-coordinate derivation be carried through for arbitrary a > 0?

**Answer**: YES. This file generalizes every step of the polar proof to a > 0:

  (∫ e^{-a x²} dx)² = ∫∫ e^{-a(x²+y²)} dx dy           [Fubini]
                    = ∫_{polar} r · e^{-a r²} dr dθ     [polar change of variables]
                    = (∫_0^∞ r · e^{-a r²} dr) · (∫_{-π}^{π} 1 dθ)   [separation]
                    = (1/(2a)) · (2π) = π/a             [radial × angular]

  Hence ∫ e^{-a x²} dx = √(π/a).

**Distinction from siblings**:
- `AreaOfCircleOQ05.scaled_gaussian` proves the same `√(π/a)` formula, but *directly*
  via Mathlib's `integral_gaussian a`. It never opens the polar derivation.
- `AreaOfCircleOQ05OQ01` does the explicit polar derivation, but only for a = 1.
This file is the missing intersection: the explicit polar derivation for general a > 0.

**Key generalization**: the radial integral becomes a-dependent,
  ∫_0^∞ r · e^{-a r²} dr = 1/(2a)   (antiderivative -(1/(2a))·e^{-a r²}),
while the angular factor 2π is unchanged — the geometric "circumference" contribution
is independent of the scale a, which is exactly why π appears with the single power 1/a.

**Sorry count**: 0. All steps fully proved.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ05
import Proofs.AreaOfCircleOQ05OQ01

open MeasureTheory Real Set Filter Prod
open scoped NNReal ENNReal

namespace AreaOfCircleOQ05OQ01Incomplete01

/-! ## Section I: Fubini — Square of the scaled Gaussian as a double integral -/

/-- **Fubini step (scaled)**: (∫ e^{-a x²})² = ∫ e^{-a(x²+y²)} dx dy. -/
theorem gaussian_sq_eq_double_integral_scaled (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, rexp (-(a * x ^ 2))) ^ 2 =
    ∫ p : ℝ × ℝ, rexp (-(a * (p.1 ^ 2 + p.2 ^ 2))) := by
  have hf : Integrable (fun x : ℝ => rexp (-(a * x ^ 2))) := integrable_exp_neg_mul_sq ha
  have hfg : Integrable (fun p : ℝ × ℝ => rexp (-(a * p.1 ^ 2)) * rexp (-(a * p.2 ^ 2)))
               (volume.prod volume) :=
    hf.mul_prod hf
  -- Factor exp(-a(x²+y²)) = exp(-a x²) · exp(-a y²)
  simp_rw [show ∀ p : ℝ × ℝ, -(a * (p.1 ^ 2 + p.2 ^ 2)) = -(a * p.1 ^ 2) + -(a * p.2 ^ 2)
           from fun _ => by ring, Real.exp_add]
  symm
  rw [integral_prod _ hfg]
  simp_rw [integral_mul_left, integral_mul_right]
  ring

/-! ## Section II: Polar change of variables -/

/-- **Polar Pythagorean identity**: (r·cos θ)² + (r·sin θ)² = r². -/
private theorem polar_sum_sq (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
  have h := Real.cos_sq_add_sin_sq θ
  calc (r * cos θ) ^ 2 + (r * sin θ) ^ 2
      = r ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [h]
    _ = r ^ 2 := mul_one _

/-- **Polar change of variables (scaled)**:
  ∫ e^{-a(x²+y²)} dx dy = ∫_{r>0, θ∈(-π,π)} r · e^{-a r²} dr dθ. -/
theorem double_integral_eq_polar_scaled (a : ℝ) :
    ∫ p : ℝ × ℝ, rexp (-(a * (p.1 ^ 2 + p.2 ^ 2))) =
    ∫ p in polarCoord.target, p.1 * rexp (-(a * p.1 ^ 2)) := by
  rw [← integral_comp_polarCoord_symm (fun p => rexp (-(a * (p.1 ^ 2 + p.2 ^ 2))))]
  apply set_integral_congr polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ _
  simp only [smul_eq_mul, polarCoord_symm_apply]
  rw [polar_sum_sq r θ]

/-! ## Section III: Angular integral = 2π (scale-independent, reused from parent) -/

/-- **Angular integral**: ∫_{-π}^{π} 1 dθ = 2π. Imported from the parent polar proof. -/
theorem angular_integral : ∫ θ in Ioo (-π) π, (1 : ℝ) = 2 * π :=
  AreaOfCircleOQ05OQ01.angular_integral

/-! ## Section IV: Radial integral = 1/(2a) — the a-dependent generalization -/

/-- **Radial integral (scaled)**: ∫_0^∞ r · e^{-a r²} dr = 1/(2a).

Proof by FTC with antiderivative F(r) = -(1/(2a))·e^{-a r²}, whose derivative is
F'(r) = r·e^{-a r²}: differentiating exp(-(a r²)) gives -(a·2r)·e^{-a r²}, and the
prefactor -(1/(2a)) cancels the -2a, leaving r·e^{-a r²}. The boundary terms are
F(0) = -1/(2a) and lim_{r→∞} F(r) = 0, so the improper integral is 0 - (-1/(2a)) = 1/(2a). -/
theorem radial_integral_scaled (a : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioi (0 : ℝ), r * rexp (-(a * r ^ 2)) = 1 / (2 * a) := by
  have ha' : a ≠ 0 := ha.ne'
  -- Derivative of the antiderivative
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun r => -(1 / (2 * a) : ℝ) * rexp (-(a * r ^ 2)))
        (x * rexp (-(a * x ^ 2))) x := by
    intro x _
    have h := ((((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(1 / (2 * a) : ℝ)))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    ring
  -- exp(-a r²) → 0 as r → ∞
  have hexp_tend : Tendsto (fun r : ℝ => rexp (-(a * r ^ 2))) atTop (nhds 0) := by
    have hpow : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have hmul : Tendsto (fun r : ℝ => a * r ^ 2) atTop atTop :=
      hpow.const_mul_atTop ha
    have hneg : Tendsto (fun r : ℝ => -(a * r ^ 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hmul
    exact tendsto_exp_atBot.comp hneg
  have htend : Tendsto (fun r : ℝ => -(1 / (2 * a) : ℝ) * rexp (-(a * r ^ 2))) atTop (nhds 0) := by
    simpa using hexp_tend.const_mul (-(1 / (2 * a) : ℝ))
  have hint : IntegrableOn (fun r => r * rexp (-(a * r ^ 2))) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv
      (fun r hr => mul_nonneg (le_of_lt hr) (exp_pos _).le) htend
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [Real.exp_zero] at h
  rw [h]
  ring

/-! ## Section V: Separation of variables — polar integral = radial × angular -/

/-- **Separation of variables (scaled)**:
  ∫_{polarCoord.target} r · e^{-a r²} = (∫_0^∞ r · e^{-a r²} dr) · (∫_{-π}^π 1 dθ). -/
theorem polar_integral_factorization_scaled (a : ℝ) (ha : 0 < a) :
    ∫ p in polarCoord.target, p.1 * rexp (-(a * p.1 ^ 2)) =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(a * r ^ 2))) *
    (∫ θ in Ioo (-π) π, (1 : ℝ)) := by
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo]
  have hval := radial_integral_scaled a ha
  -- Integrability of the radial factor (it has nonzero integral, hence is integrable)
  have hrad : Integrable (fun r : ℝ => r * rexp (-(a * r ^ 2))) (volume.restrict (Ioi 0)) := by
    by_contra h
    rw [integral_undef h] at hval
    exact absurd hval (div_pos one_pos (mul_pos two_pos ha)).ne
  haveI : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hf : Integrable (fun p : ℝ × ℝ => p.1 * rexp (-(a * p.1 ^ 2)))
              ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) :=
    hrad.comp_fst _
  rw [integral_prod _ hf]
  have h_vol : (volume (Ioo (-π) π)).toReal = π - -π := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [pi_pos])]
  simp_rw [set_integral_const, smul_eq_mul, h_vol]
  rw [integral_mul_left, angular_integral]
  ring

/-! ## Section VI: Main theorems — the explicit polar proof for the scaled Gaussian -/

/-- **2D scaled Gaussian via polar coordinates**: ∫_{ℝ²} e^{-a(x²+y²)} = π/a. -/
theorem two_dim_gaussian_scaled (a : ℝ) (ha : 0 < a) :
    ∫ p : ℝ × ℝ, rexp (-(a * (p.1 ^ 2 + p.2 ^ 2))) = π / a := by
  rw [double_integral_eq_polar_scaled a, polar_integral_factorization_scaled a ha,
      radial_integral_scaled a ha, angular_integral]
  field_simp
  ring

/-- **Polar-coordinate proof (scaled)**: (∫ e^{-a x²} dx)² = π/a. -/
theorem gaussian_integral_sq_via_polar_scaled (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, rexp (-(a * x ^ 2))) ^ 2 = π / a := by
  rw [gaussian_sq_eq_double_integral_scaled a ha, two_dim_gaussian_scaled a ha]

/-- **Scaled Gaussian integral via polar coordinates**: ∫ e^{-a x²} dx = √(π/a).

This recovers `AreaOfCircleOQ05.scaled_gaussian`, but through the *explicit* polar
derivation (Fubini + polar change of variables + radial/angular separation) rather
than Mathlib's `integral_gaussian`. -/
theorem gaussian_integral_via_polar_scaled (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, rexp (-(a * x ^ 2)) = √(π / a) := by
  have hsq := gaussian_integral_sq_via_polar_scaled a ha
  have hnn : 0 ≤ ∫ x : ℝ, rexp (-(a * x ^ 2)) :=
    integral_nonneg fun x => le_of_lt (exp_pos _)
  rw [← Real.sqrt_sq hnn, hsq]

/-! ## Section VII: Consistency checks -/

/-- Setting a = 1 recovers the unit Gaussian integral ∫ e^{-x²} = √π. -/
theorem unit_case_recovers_sqrt_pi :
    ∫ x : ℝ, rexp (-(x ^ 2)) = √π := by
  have h := gaussian_integral_via_polar_scaled 1 one_pos
  simp only [one_mul, div_one] at h
  exact h

/-! ## Verification -/

#check gaussian_integral_via_polar_scaled
#check gaussian_integral_sq_via_polar_scaled
#check two_dim_gaussian_scaled
#check radial_integral_scaled
#check unit_case_recovers_sqrt_pi

end AreaOfCircleOQ05OQ01Incomplete01
