/-
  Aristotle targets for AreaOfCircleOQ05OQ01 (Polar-Coordinate Proof of Gaussian Integral)
  Routine integration API steps for automated proof search.
  See AreaOfCircleOQ05OQ01.lean for the main formalization.

  The four sorry steps bridge the polar-coordinate proof chain:
    (∫ e^{-x²})²
      = ∫∫ e^{-(x²+y²)}      [Section I: Fubini]
      = ∫_polar r·e^{-r²}    [Section II: polar change of variables]
      = (∫_0^∞ r·e^{-r²}) · (∫_{-π}^{π} 1)   [Section V: separation]
      = (1/2) · 2π = π       [Sections III, IV]

  All four targets are technical integration API steps, not open conjectures.
  The main theorem chain (via rw) already compiles; only the four steps are sorry'd.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ05

open MeasureTheory Real Set Filter Prod
open scoped NNReal ENNReal

noncomputable section

namespace AreaOfCircleOQ05OQ01Aristotle

/-
HELPER: exp(-x²-y²) = exp(-x²) * exp(-y²).
Key algebraic identity for Fubini step.
-/
lemma rexp_neg_sum_sq (x y : ℝ) :
    rexp (-(x ^ 2 + y ^ 2)) = rexp (-(x ^ 2)) * rexp (-(y ^ 2)) := by
  rw [neg_add, Real.exp_add]

/-
HELPER: The measure of the angular domain Ioo(-π, π) is 2π.
Used in both angular_integral and polar_integral_factorization.
-/
lemma volume_angular_domain :
    (volume (Ioo (-Real.pi) Real.pi)).toReal = 2 * Real.pi := by
  rw [Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-
HELPER: Pythagorean identity in polar coordinates.
(r·cos θ)² + (r·sin θ)² = r²
-/
lemma polar_sum_sq (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
  have h := Real.cos_sq_add_sin_sq θ
  nlinarith [sq_nonneg (r * Real.cos θ), sq_nonneg (r * Real.sin θ),
             sq_nonneg r, sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

/-
TARGET 1
(∫ exp(-x²))² = ∫_{ℝ×ℝ} exp(-(x²+y²)) dxdy.

Strategy: integral_prod_mul (Fubini) converts the product of two independent
integrals to a double integral. Use rexp_neg_sum_sq to rewrite the integrand.
Specifically: (∫ f(x)) * (∫ g(y)) = ∫ (x,y), f(x)*g(y) when f, g integrable.
Here f = g = exp(-·²), and exp(-x²-y²) = exp(-x²)*exp(-y²) by rexp_neg_sum_sq.
-/
theorem gaussian_sq_eq_double_integral :
    (∫ x : ℝ, rexp (-(x ^ 2))) ^ 2 =
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) := by
  sorry

/-
TARGET 2
∫_{ℝ×ℝ} exp(-(x²+y²)) = ∫_{polarCoord.target} r · exp(-r²) drdθ.

Strategy: Apply integral_comp_polarCoord_symm to change variables to polar.
The Jacobian factor is r = p.1. After substitution:
  f(polarCoord.symm (r,θ)) = f(r·cosθ, r·sinθ) = exp(-((r·cosθ)²+(r·sinθ)²))
                            = exp(-r²)   [by polar_sum_sq]
So: ∫ p, p.1 • f(polarCoord.symm p) = ∫ p, f p, giving the result.
-/
theorem double_integral_eq_polar :
    ∫ p : ℝ × ℝ, rexp (-(p.1 ^ 2 + p.2 ^ 2)) =
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) := by
  sorry

/-
TARGET 3
∫_{-π}^{π} 1 dθ = 2π.

Strategy: set_integral_const gives ∫ x in s, c = (μ s).toReal • c.
Then Real.volume_Ioo gives volume(Ioo(-π,π)) = ENNReal.ofReal(2π).
ENNReal.toReal_ofReal (with 2π ≥ 0) completes the calculation.
-/
theorem angular_integral : ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) = 2 * Real.pi := by
  rw [set_integral_const, smul_eq_mul, mul_one]
  exact volume_angular_domain

/-
TARGET 4
∫_{polarCoord.target} r · exp(-r²) = (∫_{r>0} r·exp(-r²)) · (∫_{-π}^{π} 1).

Strategy: polarCoord.target = Ioi 0 ×ˢ Ioo(-π,π) by definition.
The integrand r·exp(-r²) factors as (r·exp(-r²)) · 1 (independent of θ).
Apply Fubini (MeasureTheory.integral_prod) on the product measure
Ioi(0) ×ˢ Ioo(-π,π) with the product Lebesgue measure.
-/
theorem polar_integral_factorization :
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2))) *
    (∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) := by
  sorry

end AreaOfCircleOQ05OQ01Aristotle

end
