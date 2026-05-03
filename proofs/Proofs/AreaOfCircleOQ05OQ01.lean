/-
# Area of Circle OQ-05-OQ-01: Polar-Coordinate Proof of the Gaussian Integral

**Open Question (OQ-01 from OQ-05)**: Can the connection between the Gaussian integral
and circle area be made fully explicit by formalizing the polar-coordinate proof?

**Answer**: YES. This file formalizes the classical derivation:

  (∫ e^{-x²} dx)² = ∫∫ e^{-(x²+y²)} dx dy  [Fubini]
                  = ∫_{polar} r · e^{-r²} dr dθ  [Change of variables: integral_comp_polarCoord_symm]
                  = (∫_0^∞ r · e^{-r²} dr) · (∫_{-π}^{π} 1 dθ)  [Separation]
                  = (1/2) · (2π) = π             [Radial × Angular]

  Hence ∫ e^{-x²} dx = √π.

**Key Lean primitive**: `integral_comp_polarCoord_symm` from Mathlib.Analysis.SpecialFunctions.PolarCoord.

**Distinction from AreaOfCircleOQ05**: That file uses Mathlib's `integral_gaussian` directly.
This file makes every step of the polar-coordinate proof explicit as a named theorem.

**Sorry count**: 2 (product integrability for Fubini in Sections I and V).
angular_integral (∫_{-π}^{π} 1 = 2π) is proved via set_integral_const + volume_Ioo.
double_integral_eq_polar is proved via integral_comp_polarCoord_symm + set_integral_congr.
The main chain `gaussian_integral_sq_via_polar` compiles modulo the 2 integrability sorries.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ05

open MeasureTheory Real Set Filter Prod
open scoped NNReal ENNReal

namespace AreaOfCircleOQ05OQ01

/-! ## Section I: Fubini — Square of Gaussian as Double Integral

The Fubini step rewrites (∫ f)² as ∫∫ f(x)·f(y) via the product measure:
  (∫ exp(-x²))² = (∫ exp(-x²))(∫ exp(-y²)) = ∫ exp(-x²-y²) dx dy

Strategy: integral_mul_right + integral_mul_left + integral_prod (Fubini-Tonelli). -/

/-- **Fubini step**: (∫ exp(-x²))² = ∫ exp(-(x²+y²)) dx dy.

Proof: factor exp(-(p.1²+p.2²)) = exp(-p.1²)·exp(-p.2²) via exp_add, then apply
Fubini (integral_prod) to write ∫∫ f(x)·g(y) as (∫ f)·(∫ g) via integral_mul_left/right.
[Sorry: product integrability of Gaussian factors on ℝ²] -/
theorem gaussian_sq_eq_double_integral :
    (∫ x : ℝ, rexp (-(x ^ 2))) ^ 2 =
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) := by
  have hf : Integrable (fun x : ℝ => rexp (-(x ^ 2))) := by
    have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    simp_rw [one_mul] at h; exact h
  have hfg : Integrable (fun p : ℝ × ℝ => rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2)))
               (volume.prod volume) := by
    sorry  -- HARD: product of integrable Gaussian factors is integrable on ℝ²
  -- Factor integrand using exp(a + b) = exp(a) * exp(b)
  simp_rw [show ∀ p : ℝ × ℝ, -(p.1 ^ 2 + p.2 ^ 2) = -(p.1 ^ 2) + -(p.2 ^ 2)
           from fun _ => by ring, Real.exp_add]
  -- Apply Fubini and simplify via integral linearity
  symm
  rw [integral_prod _ hfg]
  simp_rw [integral_mul_left, integral_mul_right]
  ring

/-! ## Section II: Polar Change of Variables

The polar coordinates in ℝ²: polarCoord : PartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)
  - Source: ℝ² \ {(x,y) : x ≤ 0} (a.e. all of ℝ²)
  - Target: Ioi(0) ×ˢ Ioo(-π,π) = {(r,θ) : r > 0, -π < θ < π}
  - polarCoord.symm (r,θ) = (r·cos θ, r·sin θ)

Key theorem: `integral_comp_polarCoord_symm`:
  ∫ p in polarCoord.target, p.1 • f(polarCoord.symm p) = ∫ p, f p -/

/-- **Polar Pythagorean identity**: (r·cos θ)² + (r·sin θ)² = r². -/
private theorem polar_sum_sq (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
  have h := Real.cos_sq_add_sin_sq θ
  calc (r * cos θ) ^ 2 + (r * sin θ) ^ 2
      = r ^ 2 * cos θ ^ 2 + r ^ 2 * sin θ ^ 2 := by ring
    _ = r ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [h]
    _ = r ^ 2 := mul_one _

/-- **Polar change of variables**: The 2D Gaussian integral equals the polar integral.

  ∫ exp(-(x²+y²)) dx dy = ∫_{r>0, θ∈(-π,π)} r · exp(-r²) dr dθ

Proof: apply `integral_comp_polarCoord_symm` (change of variables — rewrites LHS to polar form),
then show the integrands are equal pointwise via `set_integral_congr`:
  r • exp(-((r·cosθ)²+(r·sinθ)²)) = r * exp(-r²)  [by polarCoord_symm_apply + polar_sum_sq]. -/
theorem double_integral_eq_polar :
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) =
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) := by
  rw [← integral_comp_polarCoord_symm (fun p => rexp (-(p.1 ^ 2 + p.2 ^ 2)))]
  apply set_integral_congr polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ _
  simp only [smul_eq_mul, polarCoord_symm_apply]
  rw [polar_sum_sq r θ]

/-! ## Section III: Angular Integral = 2π

The angular integral ∫_{-π}^{π} 1 dθ = 2π is the circumference factor that
explains why π appears in the Gaussian integral. -/

/-- **Angular integral**: ∫_{-π}^{π} 1 dθ = 2π.

The proof chain:
  ∫ θ in Ioo (-π) π, 1
  = (volume (Ioo (-π) π)).toReal  [by integral_const + restrict_apply_univ]
  = ENNReal.toReal (ENNReal.ofReal (π - (-π)))  [by Real.volume_Ioo]
  = π - (-π) = 2π  [by toReal_ofReal + ring]
[Sorry: Measure.restrict_apply_univ is in the API but simp chaining needs careful setup] -/
theorem angular_integral : ∫ θ in Ioo (-π) π, (1 : ℝ) = 2 * π := by
  rw [set_integral_const, smul_eq_mul, mul_one, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [pi_pos])]
  ring

/-! ## Section IV: Radial Integral = 1/2

The radial integral ∫_0^∞ r·e^{-r²} dr = 1/2 via the substitution u = r². -/

/-- **Radial integral**: ∫_0^∞ r · exp(-r²) dr = 1/2.
    Imported from AreaOfCircleOQ05 (proved via FTC with antiderivative -(1/2)·exp(-r²)). -/
theorem radial_integral_eq :
    ∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2)) = 1 / 2 :=
  GaussianIntegralCircle.radial_integral

/-! ## Section V: Factorization of Polar Integral

The polar integral over Ioi(0) ×ˢ Ioo(-π,π) factors as radial × angular
because the integrand r·exp(-r²) is independent of θ. -/

/-- **Separation of variables**: The polar integral = radial × angular.
  ∫_{polarCoord.target} r · exp(-r²) = (∫_0^∞ r · exp(-r²) dr) · (∫_{-π}^π 1 dθ)

Proof:
  1. Rewrite target = Ioi(0) ×ˢ Ioo(-π,π) via polarCoord_target.
  2. Convert set integral to product-measure integral via Measure.restrict_prod_eq_prod_restrict.
  3. Apply Fubini (integral_prod): iterated integral over r × θ.
  4. Inner integral (const in θ): integral_const + volume_Ioo gives factor (π - -π) = 2π.
  5. Pull constant out: integral_mul_left. Close with angular_integral + ring.
[Sorry: integrability of radial factor on product measure] -/
theorem polar_integral_factorization :
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2))) *
    (∫ θ in Ioo (-π) π, (1 : ℝ)) := by
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo]
  -- Integrability for radial component (from radial_integral_eq ≠ 0)
  have hrad : Integrable (fun r : ℝ => r * rexp (-(r ^ 2))) (volume.restrict (Ioi 0)) := by
    by_contra h
    simp only [integral_undef h] at radial_integral_eq
    norm_num at radial_integral_eq
  -- Apply Fubini: ∫ ∂(μ.prod ν) = ∫ ∂μ, ∫ ∂ν
  have hf : Integrable (fun p : ℝ × ℝ => p.1 * rexp (-(p.1 ^ 2)))
              ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) := by
    sorry  -- HARD: hrad + finite angular measure → product integrability
  rw [integral_prod _ hf]
  -- Inner integral (constant in θ): ∫ θ in Ioo(-π,π), r·exp(-r²) = (vol Ioo) * r·exp(-r²)
  have h_vol : (volume (Ioo (-π) π)).toReal = π - -π := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [pi_pos])]
  simp_rw [set_integral_const, smul_eq_mul, h_vol]
  -- ∫ r in Ioi 0, (π - -π) * (r * exp(-r²)) = (∫ r in Ioi 0, r * exp(-r²)) * (∫ θ, 1)
  rw [integral_mul_left, angular_integral]
  ring

/-! ## Section VI: Main Theorem — Polar-Coordinate Proof of (∫ e^{-x²})² = π -/

/-- **Polar-coordinate proof**: (∫ e^{-x²} dx)² = π.

Explicit chain:
  (∫ exp(-x²))²
    = ∫ p : ℝ², exp(-(x²+y²))      [Section I: Fubini]
    = ∫_polar r · exp(-r²) dr dθ   [Section II: polar change of variables]
    = (∫_0^∞ r·exp(-r²) dr) · 2π  [Section V: separation]
    = (1/2) · 2π = π               [Sections III, IV: radial=1/2, angular=2π]

This makes explicit the connection: π appears because the angular integral = 2π
(circumference factor) and the radial integral contributes 1/2. -/
theorem gaussian_integral_sq_via_polar :
    (∫ x : ℝ, rexp (-(x ^ 2))) ^ 2 = π := by
  rw [gaussian_sq_eq_double_integral, double_integral_eq_polar,
      polar_integral_factorization, radial_integral_eq, angular_integral]
  ring

/-- **Gaussian integral via polar coordinates**: ∫ e^{-x²} dx = √π. -/
theorem gaussian_integral_via_polar :
    ∫ x : ℝ, rexp (-(x ^ 2)) = √π := by
  have hsq := gaussian_integral_sq_via_polar
  have hnn : 0 ≤ ∫ x : ℝ, rexp (-(x ^ 2)) :=
    integral_nonneg fun x => le_of_lt (exp_pos _)
  rw [← Real.sqrt_sq hnn, hsq]

/-! ## Section VII: Connection to Circle Area

The polar decomposition makes explicit why π appears in the Gaussian integral:
- **Angular factor 2π**: This is the circumference of the unit circle, arising from
  the θ integration over (-π, π)
- **Radial factor 1/2**: From ∫_0^∞ r·e^{-r²} dr = 1/2 via substitution u = r²
- **Product**: (1/2) · 2π = π = area of unit circle

The Gaussian integral secretly computes the area element integral ∫∫ e^{-r²} r dr dθ
over all of ℝ², which factors via the circular symmetry. -/

/-- The polar decomposition shows: (∫ e^{-x²})² = radial × angular = (1/2) · 2π. -/
theorem gaussian_sq_eq_radial_times_angular :
    (∫ x : ℝ, rexp (-(x ^ 2))) ^ 2 =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2))) * (∫ θ in Ioo (-π) π, (1 : ℝ)) := by
  rw [gaussian_sq_eq_double_integral, double_integral_eq_polar, polar_integral_factorization]

/-- The angular integral 2π comes from the circle's circumference. -/
theorem angular_integral_is_circumference :
    ∫ θ in Ioo (-π) π, (1 : ℝ) = 2 * π := angular_integral

/-! ## Verification -/

#check gaussian_integral_sq_via_polar
#check gaussian_integral_via_polar
#check angular_integral
#check radial_integral_eq
#check double_integral_eq_polar

end AreaOfCircleOQ05OQ01
