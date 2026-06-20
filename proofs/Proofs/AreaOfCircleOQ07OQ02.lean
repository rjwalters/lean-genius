import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Half-Line Gaussian Integral Equals √(π/b)/2

## Open Question (area-of-circle-oq-07-oq-02)
The parent entry `area-of-circle-oq-07` evaluates the *full-line* Gaussian
`∫_ℝ e^{-x²} dx = √π`.  This entry records its half-line companion:

$$ \int_{0}^{\infty} e^{-b x^2}\, dx = \frac{1}{2}\sqrt{\frac{\pi}{b}}
   \qquad (b > 0). $$

## Answer: YES — it is `integral_gaussian_Ioi` from Mathlib.

Mathlib's `integral_gaussian_Ioi (b : ℝ) : ∫ x in Ioi 0, exp (-b * x ^ 2) = √(π / b) / 2`
already evaluates the half-line Gaussian for every real `b` (for `b ≤ 0` both
sides are `0`, so no positivity hypothesis is needed).  Setting `b = 1` collapses
the integrand `exp (-1 · x²)` to `exp (-x²)` via `neg_one_mul` and the value
`√(π/1)/2` to `√π/2` via `div_one`.

The mathematically substantive content here is the **even-symmetry bridge to the
parent**: because `x ↦ e^{-x²}` is even, the full-line integral is exactly twice
the half-line integral,
`∫_ℝ e^{-x²} = 2 ∫_{(0,∞)} e^{-x²}`,
which we verify by reducing both sides to their closed forms `√π` and `√π/2`.
This makes the parent's `√π` and this entry's `√π/2` a consistent pair, with the
factor of `2` being precisely the even-symmetry doubling.

No new axioms: the proof is a routine specialization of existing Mathlib results.
-/

open Real MeasureTheory

/-- **The half-line Gaussian integral.** For every real `b`, the integral of
`e^{-b x²}` over `(0, ∞)` is `√(π/b)/2`.  (For `b ≤ 0` both sides vanish.) -/
theorem gaussian_integral_Ioi (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * x ^ 2)) = Real.sqrt (Real.pi / b) / 2 :=
  integral_gaussian_Ioi b

/-- The `b = 1` specialization: `∫_{(0,∞)} e^{-x²} = √π/2`. -/
theorem gaussian_integral_Ioi_one :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2)) = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi 1
  simpa only [neg_one_mul, div_one] using h

/-- **Even-symmetry bridge to the parent.** Since `e^{-x²}` is even, the full-line
Gaussian `∫_ℝ e^{-x²} = √π` (parent `area-of-circle-oq-07`) is exactly twice the
half-line value `√π/2`. -/
theorem gaussian_integral_eq_two_mul_Ioi :
    (∫ x : ℝ, Real.exp (-x ^ 2))
      = 2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) := by
  have hfull : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul, div_one] using integral_gaussian 1
  rw [hfull, gaussian_integral_Ioi_one]
  ring
