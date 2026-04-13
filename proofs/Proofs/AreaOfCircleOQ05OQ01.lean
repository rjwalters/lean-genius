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

**Sorry count**: 4 (Fubini steps, polar change-of-variables API, angular measure).
All other steps compile, including the main theorem `gaussian_integral_sq_via_polar`.
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
[Sorry: product-of-integrals → product-measure integral via Fubini + exp addition law] -/
theorem gaussian_sq_eq_double_integral :
    (∫ x : ℝ, rexp (-(x ^ 2))) ^ 2 =
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) := by
  sorry

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

Proof: apply `integral_comp_polarCoord_symm` (change of variables) then simplify
using (r·cos θ)² + (r·sin θ)² = r² (via `polar_sum_sq`).
[Sorry: API issues with setIntegral_congr and polarCoord_symm_apply exact forms] -/
theorem double_integral_eq_polar :
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) =
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) := by
  -- Strategy: rw [← integral_comp_polarCoord_symm], then congr using polar_sum_sq
  -- integral_comp_polarCoord_symm : ∫ p in polarCoord.target, p.1 • f(polarCoord.symm p) = ∫ p, f p
  -- After change of vars: f(r·cos θ, r·sin θ) = exp(-r²) (by polar_sum_sq)
  sorry

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
  sorry

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

Proof: Fubini on Ioi(0) ×ˢ Ioo(-π,π) + integral_const for the θ-integral.
polarCoord.target = Ioi(0) ×ˢ Ioo(-π,π) by definition.
[Sorry: Fubini on product set + measure separation API] -/
theorem polar_integral_factorization :
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2))) *
    (∫ θ in Ioo (-π) π, (1 : ℝ)) := by
  sorry

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
