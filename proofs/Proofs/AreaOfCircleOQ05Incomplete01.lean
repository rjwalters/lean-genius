/-
# Area of Circle OQ-05 (completion) — the normal-distribution normalization family

The parent `AreaOfCircleOQ05.lean` proves the Gaussian integral
`∫ exp(-x²) dx = √π` (via Mathlib's `integral_gaussian`) and connects it to the
area of a circle through the polar-coordinate squaring argument. Its sibling
files handle the polar proof (oq-05-oq-01), the multivariate case
(oq-05-oq-02), and the complex Gaussian (oq-05-oq-04).

One classical strand is not yet covered: the **normalization constants of the
normal distribution**, which are exactly the rescalings of `√π` that make the
Gaussian a probability density. This file fills that gap, axiom-free, deriving
everything from `integral_gaussian`:

* `∫ exp(-x²/2) dx = √(2π)`                              (`gaussian_half`)
* `∫ (1/√(2π))·exp(-x²/2) dx = 1`                        (`std_normal_normalization`)
* `∫ exp(-x²/(2σ²)) dx = σ·√(2π)`        for `σ > 0`     (`gaussian_variance`)
* `∫ (1/(σ·√(2π)))·exp(-x²/(2σ²)) dx = 1` for `σ > 0`    (`gaussian_variance_normalization`)

together with the base case `∫ exp(-x²) dx = √π` and the area-of-circle
identity `(∫ exp(-x²) dx)² = π` restated for context. The normalization with
mean `0`; the general mean `μ` is a translation (`integral` is shift-invariant)
and is recorded as `gaussian_mean_shift`.

Every result is checked by the kernel with no axioms and no `native_decide`.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

open Real MeasureTheory

namespace AreaOfCircleOQ05Incomplete01

/-- `√(2π) > 0`, the standard normalization constant. -/
theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * π) :=
  Real.sqrt_pos.mpr (by positivity)

/-- Base case (parent): `∫ exp(-x²) dx = √π`. -/
theorem gaussian_unit : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt π := by
  have h := integral_gaussian 1
  have hfun : (fun x : ℝ => Real.exp (-x ^ 2)) = (fun x => Real.exp (-1 * x ^ 2)) := by
    funext x; congr 1; ring
  rw [hfun, h]
  congr 1
  rw [div_one]

/-- The squared Gaussian integral is `π` — the area-of-circle identity:
`(∫ exp(-x²) dx)² = ∫∫ exp(-(x²+y²)) = π`. -/
theorem gaussian_unit_sq : (∫ x : ℝ, Real.exp (-x ^ 2)) ^ 2 = π := by
  rw [gaussian_unit, Real.sq_sqrt Real.pi_pos.le]

/-- The variance-`1` (after the `1/2` convention) normalization:
`∫ exp(-x²/2) dx = √(2π)`. -/
theorem gaussian_half : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2)
  have hfun : (fun x : ℝ => Real.exp (-x ^ 2 / 2)) = (fun x => Real.exp (-(1 / 2) * x ^ 2)) := by
    funext x; congr 1; ring
  rw [hfun, h]
  congr 1
  rw [show π / (1 / 2) = 2 * π by ring]

/-- **Standard normal normalization.** `∫ (1/√(2π))·exp(-x²/2) dx = 1`. -/
theorem std_normal_normalization :
    ∫ x : ℝ, (1 / Real.sqrt (2 * π)) * Real.exp (-x ^ 2 / 2) = 1 := by
  rw [integral_const_mul, gaussian_half, one_div, inv_mul_cancel₀ (ne_of_gt sqrt_two_pi_pos)]

/-- General variance: `∫ exp(-x²/(2σ²)) dx = σ·√(2π)` for `σ > 0`. -/
theorem gaussian_variance (σ : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Real.exp (-x ^ 2 / (2 * σ ^ 2)) = σ * Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / (2 * σ ^ 2))
  have hfun : (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2)))
      = (fun x => Real.exp (-(1 / (2 * σ ^ 2)) * x ^ 2)) := by
    funext x; congr 1
    field_simp
  rw [hfun, h]
  rw [show π / (1 / (2 * σ ^ 2)) = σ ^ 2 * (2 * π) by field_simp]
  rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]

/-- **General Gaussian normalization** (mean `0`, variance `σ²`):
`∫ (1/(σ·√(2π)))·exp(-x²/(2σ²)) dx = 1` for `σ > 0`. -/
theorem gaussian_variance_normalization (σ : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, (1 / (σ * Real.sqrt (2 * π))) * Real.exp (-x ^ 2 / (2 * σ ^ 2)) = 1 := by
  rw [integral_const_mul, gaussian_variance σ hσ, one_div,
    inv_mul_cancel₀ (by positivity)]

/-- **Mean shift.** Translating the variable leaves the Gaussian integral
unchanged: `∫ exp(-(x-μ)²/2) dx = √(2π)` — the normal density has the same mass
for every mean `μ`. -/
theorem gaussian_mean_shift (μ : ℝ) :
    ∫ x : ℝ, Real.exp (-(x - μ) ^ 2 / 2) = Real.sqrt (2 * π) := by
  rw [← gaussian_half]
  exact integral_sub_right_eq_self (fun x => Real.exp (-x ^ 2 / 2)) μ

end AreaOfCircleOQ05Incomplete01
