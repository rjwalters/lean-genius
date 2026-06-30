import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Gaussian Integral Equals √π

## Open Question (area-of-circle-oq-07)
"The total integral of the Gaussian bell curve `e^{-x²}` over the whole real
line equals `√π`."

$$ \int_{-\infty}^{\infty} e^{-x^2}\, dx = \sqrt{\pi}. $$

## Answer: YES — it is the `b = 1` specialization of the general Gaussian integral.

Mathlib's `integral_gaussian (b : ℝ) : ∫ x, exp (-b * x ^ 2) = √(π / b)` already
evaluates the parametrized Gaussian integral for every real `b`.  Setting `b = 1`
turns the integrand `exp (-1 * x ^ 2)` into `exp (-x ^ 2)` (via `neg_one_mul`) and
the value `√(π / 1)` into `√π` (via `div_one`), giving the classical normalization
constant behind the standard normal distribution.

The classical evaluation squares the integral and passes to polar coordinates,
where the circle-area Jacobian — the subject of the parent entry `area-of-circle`
— appears.  The corollary `gaussian_integral_sq` records that squared identity
`(∫ e^{-x²})² = π`, the algebraic heart of that polar-coordinate argument.

No new axioms: the proof is a routine specialization of an existing Mathlib result.
-/

open Real MeasureTheory

/-- **The Gaussian integral.** The integral of `e^{-x²}` over all of `ℝ` is `√π`. -/
theorem gaussian_integral_eq_sqrt_pi :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simpa only [neg_one_mul, div_one] using h

/-- The squared Gaussian integral equals `π` — the identity obtained by squaring
`∫ e^{-x²}` and evaluating the resulting planar integral in polar coordinates. -/
theorem gaussian_integral_sq :
    (∫ x : ℝ, Real.exp (-x ^ 2)) ^ 2 = Real.pi := by
  rw [gaussian_integral_eq_sqrt_pi, Real.sq_sqrt Real.pi_nonneg]
