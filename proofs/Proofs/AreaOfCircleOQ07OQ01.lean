import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Standard Normal Density Integrates to One

## Open Question (area-of-circle-oq-07-oq-01)
"Formalize the normalized standard-normal density: prove

$$ \int_{-\infty}^{\infty} \frac{1}{\sqrt{2\pi}}\, e^{-x^2/2}\, dx = 1, $$

deriving it from `integral_gaussian` at `b = 1/2` together with the `√π` value,
to connect this normalization directly to probability theory."

## Answer: YES — it is the `b = 1/2` specialization of the parametrized Gaussian.

The parent entry `area-of-circle-oq-07` evaluates the bare Gaussian
`∫ e^{-x²} = √π` as the `b = 1` case of Mathlib's
`integral_gaussian (b : ℝ) : ∫ x, exp (-b * x ^ 2) = √(π / b)`.

Taking instead `b = 1/2` turns the integrand `exp (-(1/2)·x²) = exp (-x²/2)`
into the Gaussian kernel of the *standard normal distribution* (mean `0`,
variance `1`), and the value `√(π / (1/2)) = √(2π)` into its normalization
constant.  Dividing by `√(2π)` therefore yields a probability density of total
mass `1` — the defining property that makes `N(0,1)` a probability measure.

Two facts are recorded:

* `integral_exp_neg_half_sq` : `∫ e^{-x²/2} = √(2π)`, the un-normalized mass of
  the variance-`1` Gaussian, obtained directly from `integral_gaussian (1/2)`.
* `standard_normal_density_integral_eq_one` : `∫ (1/√(2π))·e^{-x²/2} = 1`, the
  normalization, obtained by pulling the constant out of the integral
  (`integral_const_mul`) and cancelling `(√(2π))⁻¹ · √(2π) = 1`.

No new axioms: both proofs are routine specializations of an existing Mathlib
result, the same analytic content (squaring and polar coordinates, where the
circle-area Jacobian of the grandparent entry `area-of-circle` appears) being
already discharged inside `integral_gaussian`.
-/

open Real MeasureTheory

/-- The Gaussian kernel of the standard normal distribution integrates to its
normalization constant: `∫ e^{-x²/2} = √(2π)`.  This is the `b = 1/2` case of
Mathlib's parametrized Gaussian integral, since `-x²/2 = -(1/2)·x²` and
`π / (1/2) = 2π`. -/
theorem integral_exp_neg_half_sq :
    (∫ x : ℝ, Real.exp (-x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
  have key : ∀ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.exp (-(1 / 2) * x ^ 2) := by
    intro x; congr 1; ring
  simp_rw [key]
  rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]

/-- **The standard normal density integrates to one.**
`∫ (1/√(2π))·e^{-x²/2} = 1`, the total mass of the `N(0,1)` probability density.
Obtained from `integral_exp_neg_half_sq` by pulling out the constant factor and
cancelling `(√(2π))⁻¹ · √(2π) = 1`. -/
theorem standard_normal_density_integral_eq_one :
    (∫ x : ℝ, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x ^ 2 / 2)) = 1 := by
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_half_sq, one_div,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity))]
