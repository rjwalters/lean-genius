import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Half-Line Gaussian Integral

## Open Question (area-of-circle-oq-07-oq-02)
"What is the value of the Gaussian integral taken over the positive half-line
`(0, ∞)` instead of all of `ℝ`?"

$$ \int_{0}^{\infty} e^{-b x^2}\, dx = \tfrac{1}{2}\sqrt{\tfrac{\pi}{b}}. $$

## Answer: it is exactly half of the full-line value `√(π/b)`.

The parent entry `area-of-circle-oq-07` evaluates the **full-line** Gaussian
`∫_{-∞}^{∞} e^{-x²} dx = √π`.  Because the integrand `e^{-b x²}` is even, the
positive half-line carries exactly half of the total mass, so the half-line
integral is `√(π/b)/2`.  Mathlib's `integral_gaussian_Ioi` records this value
directly (and, like the full-line version, evaluates to `0` for `b ≤ 0`, where
the integrand fails to be integrable).

What makes this a genuine extension of the parent rather than a notational
variant is the **even-symmetry bridge**: we prove that the full-line integral is
*twice* the half-line one (`gaussian_full_eq_two_mul_half`, via
`integral_comp_abs`), and then use the half-line value at `b = 1` to *re-derive*
the parent's `√π` along a completely different route — through `Set.Ioi 0` and
even symmetry rather than through the parametrized `integral_gaussian`.

No new axioms: every step is a routine consequence of existing Mathlib results.
-/

open Real MeasureTheory

/-- **The half-line Gaussian integral.** For every real `b`, the integral of
`e^{-b x²}` over the positive half-line `(0, ∞)` equals `√(π/b)/2`. -/
theorem half_gaussian_integral (b : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) / 2 :=
  integral_gaussian_Ioi b

/-- **Even-symmetry bridge.** The full-line Gaussian integral is exactly twice
the half-line one, because `e^{-x²}` is an even function. -/
theorem gaussian_full_eq_two_mul_half :
    (∫ x : ℝ, Real.exp (-x ^ 2))
      = 2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) := by
  have heven : (∫ x : ℝ, Real.exp (-x ^ 2))
      = ∫ x : ℝ, Real.exp (-(|x|) ^ 2) := by
    simp [sq_abs]
  rw [heven]
  exact integral_comp_abs (f := fun y : ℝ => Real.exp (-y ^ 2))

/-- The half-line Gaussian at `b = 1`: `∫_{0}^{∞} e^{-x²} dx = √π / 2`. -/
theorem half_gaussian_integral_one :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  have h := half_gaussian_integral 1
  simpa only [neg_one_mul, div_one] using h

/-- **Recovering the parent.** Re-derive `∫_{-∞}^{∞} e^{-x²} dx = √π` from the
half-line value via the even-symmetry bridge — an independent route to the
parent entry `area-of-circle-oq-07`, going through `Set.Ioi 0` rather than the
parametrized full-line `integral_gaussian`. -/
theorem gaussian_integral_eq_sqrt_pi :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  rw [gaussian_full_eq_two_mul_half, half_gaussian_integral_one]
  ring
