import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-
# The Gaussian area integral: ∫_{ℝ²} e^{-b(x²+y²)} = π/b directly via Fubini + polar coordinates

## Open Question (area-of-circle-oq-07-oq-04-oq-01)
The parent `area-of-circle-oq-07-oq-04` evaluates the *square* of the one-dimensional
Gaussian integral, `(∫_ℝ e^{-b x²})² = π/b`, by **squaring** Mathlib's closed form
`∫_ℝ e^{-b x²} = (π/b)^{1/2}`.  This follow-up asks for the genuinely two-dimensional
derivation: prove

    (∫_ℝ e^{-b x²})²  =  ∫_{ℝ²} e^{-b(x²+y²)}                    (Fubini)
    ∫_{ℝ²} e^{-b(x²+y²)}  =  π/b                                  (polar change of variables)

so that `π/b` appears as the **literal area integral of the radially symmetric Gaussian**
over the plane — not as the algebraic square of the one-dimensional value.

## Answer: YES.  (real `b > 0`)

* `gaussian_sq_eq_integral_plane` — Fubini: the square of the line integral is the integral
  of the *product* Gaussian `e^{-b x²}·e^{-b y²} = e^{-b(x²+y²)}` over `ℝ²`, via
  `MeasureTheory.integral_prod_mul` and `Real.exp_add`.
* `integral_Ioi_mul_exp_neg_mul_sq` — the radial primitive integral
  `∫_{0}^{∞} r e^{-b r²} dr = 1/(2b)`, obtained from Mathlib's complex
  `integral_mul_cexp_neg_mul_sq` by pushing through `ℝ ↪ ℂ`.
* `integral_plane_radial_eq` — the **area form**: the change of variables
  `(x,y) = (r cos θ, r sin θ)` (`integral_comp_polarCoord_symm`, Jacobian `r`) collapses
  the radially symmetric integrand to `r e^{-b r²}`, and the `θ`-integral over `(-π, π)`
  contributes the length `2π`, giving `(2b)⁻¹ · 2π = π/b`.
* `gaussian_sq_eq_pi_div_b` — chains the two halves: `(∫_ℝ e^{-b x²})² = π/b`, but *routed
  through the 2-D area integral* rather than through `(π/b)^{1/2}`.
* `gaussian_sq_eq_pi` — the `b = 1` area statement `(∫_ℝ e^{-x²})² = π`.

This is the classical "Gaussian polar trick" that underlies the area-of-a-circle constant
`π`; here it is reconstructed for the real radial Gaussian from Mathlib's polar-coordinate
change-of-variables theorem.  No new axioms.
-/

open Real MeasureTheory Set

namespace AreaOfCircleOQ07OQ04OQ01

variable {b : ℝ}

/-- **Radial primitive integral.** `∫_{0}^{∞} r · e^{-b r²} dr = 1/(2b)` for `b > 0`.
Obtained from Mathlib's complex radial integral `integral_mul_cexp_neg_mul_sq` by pushing
the real integrand through the embedding `ℝ ↪ ℂ`. -/
theorem integral_Ioi_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hbc : 0 < (b : ℂ).re := by simpa using hb
  have key : (∫ r in Ioi (0 : ℝ), (r : ℂ) * Complex.exp (-(b : ℂ) * (r : ℂ) ^ 2))
      = (2 * (b : ℂ))⁻¹ := integral_mul_cexp_neg_mul_sq hbc
  have hcong : (∫ r in Ioi (0 : ℝ), ((r * Real.exp (-b * r ^ 2) : ℝ) : ℂ))
      = ∫ r in Ioi (0 : ℝ), (r : ℂ) * Complex.exp (-(b : ℂ) * (r : ℂ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    push_cast [Complex.ofReal_exp]
    ring
  have hofR : ((∫ r in Ioi (0 : ℝ), r * Real.exp (-b * r ^ 2) : ℝ) : ℂ) = (2 * (b : ℂ))⁻¹ := by
    rw [← integral_ofReal, hcong, key]
  have hcast : ((∫ r in Ioi (0 : ℝ), r * Real.exp (-b * r ^ 2) : ℝ) : ℂ)
      = (((2 * b)⁻¹ : ℝ) : ℂ) := by
    rw [hofR]; push_cast; ring
  exact_mod_cast hcast

/-- **Fubini step.** The square of the one-dimensional Gaussian integral equals the integral
over the plane of the product Gaussian `e^{-b x²}·e^{-b y²} = e^{-b(x²+y²)}`. -/
theorem gaussian_sq_eq_integral_plane (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2)) ^ 2
      = ∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) := by
  rw [pow_two, ← integral_prod_mul (fun x : ℝ => Real.exp (-b * x ^ 2))
        (fun y : ℝ => Real.exp (-b * y ^ 2))]
  congr 1
  ext1 p
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Area form (polar change of variables).** The two-dimensional integral of the radially
symmetric Gaussian over the whole plane is exactly `π/b`. The substitution
`(x, y) = (r cos θ, r sin θ)` (Jacobian `r`) reduces it to `(∫_{0}^{∞} r e^{-b r²}) · 2π`. -/
theorem integral_plane_radial_eq (hb : 0 < b) :
    (∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) = π / b := by
  have hbne : b ≠ 0 := hb.ne'
  rw [← integral_comp_polarCoord_symm (fun p : ℝ × ℝ => Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))]
  have hsimp : ∀ p ∈ polarCoord.target,
      p.1 • Real.exp (-b * ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2))
        = (p.1 * Real.exp (-b * p.1 ^ 2)) * (1 : ℝ) := by
    intro p _
    have hs : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    rw [hs]
    simp only [smul_eq_mul, mul_one]
    have hrad : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    rw [hrad]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hsimp]
  rw [show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl]
  rw [setIntegral_prod_mul (fun r : ℝ => r * Real.exp (-b * r ^ 2)) (fun _ : ℝ => (1 : ℝ))
        (Ioi (0 : ℝ)) (Ioo (-π) π)]
  rw [integral_Ioi_mul_exp_neg_mul_sq hb, setIntegral_const,
      volume_real_Ioo_of_le (by linarith [pi_pos])]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- **The Gaussian area identity.** `(∫_ℝ e^{-b x²})² = π/b`, derived through the literal
two-dimensional area integral `∫_{ℝ²} e^{-b(x²+y²)}` — Fubini then polar coordinates —
rather than by squaring the one-dimensional closed form `(π/b)^{1/2}`. -/
theorem gaussian_sq_eq_pi_div_b (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2)) ^ 2 = π / b := by
  rw [gaussian_sq_eq_integral_plane hb, integral_plane_radial_eq hb]

/-- The `b = 1` area form: `(∫_ℝ e^{-x²})² = π`, the constant attached to the area of a
disc, realized as the area integral of the unit radial Gaussian over the plane. -/
theorem gaussian_sq_eq_pi :
    (∫ x : ℝ, Real.exp (-x ^ 2)) ^ 2 = π := by
  have h := gaussian_sq_eq_pi_div_b (b := 1) one_pos
  simpa using h

end AreaOfCircleOQ07OQ04OQ01
