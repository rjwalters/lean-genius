/-
# Antiderivative of `1/√(1 + x²)`: the `arsinh` calculus capstone

Research: arsinh-log-formula-oq-01-oq-01
Parent:   arsinh-log-formula-oq-01 (logarithmic form + addition law)

This file answers the parent's first listed open question verbatim:

  > Establish `∫ 1/√(1 + x²) dx = arsinh x + C` from `hasDerivAt_arsinh`.

The parent established the *algebraic* theory of `arsinh` (its logarithmic
closed form `arsinh x = log(x + √(1 + x²))`, the addition / subtraction /
doubling laws, and concrete values such as `arsinh (4/3) = log 3`).  What was
missing was the *calculus* side: that `arsinh` is an antiderivative of the
integrand `1/√(1 + x²)`, and the resulting definite-integral evaluations.

Here we supply that capstone, all `0`-axiom and machine-checked:

* `hasDerivAt_arsinh'` — the antiderivative fact `(arsinh)' x = 1/√(1 + x²)`
  in fractional form (Mathlib states it with an inverse), i.e. the precise
  "`arsinh x + C`" content of the open question.
* `deriv_arsinh_eq` — the same as a `deriv` equation.
* `integral_one_div_sqrt_one_add_sq` — the Fundamental Theorem of Calculus
  evaluation `∫_a^b 1/√(1 + t²) dt = arsinh b − arsinh a`.
* `integral_eq_log_sub_log` — its logarithmic closed form.
* `integral_zero_to` / `integral_zero_to_log` — the `∫_0^b` normalisation
  (the genuine "`+ C` with `C = 0`" antiderivative).
* `integral_symmetric` — the even-integrand identity
  `∫_{-a}^a 1/√(1 + t²) dt = 2·arsinh a`.
* `integral_zero_to_three_quarters`, `integral_zero_to_four_thirds` — concrete
  evaluations `= log 2` and `= log 3`, tying the calculus back to the parent's
  closed-form values.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ01

open Real intervalIntegral MeasureTheory

/-- The denominator `√(1 + x²)` is strictly positive, so the integrand
`1/√(1 + x²)` is well defined and continuous everywhere. -/
theorem sqrt_one_add_sq_pos (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

/-- **Antiderivative fact (the open question).** `arsinh` is an antiderivative of
`1/√(1 + x²)`: `HasDerivAt arsinh (1/√(1 + x²)) x` at every real `x`.

Mathlib's `Real.hasDerivAt_arsinh` records the derivative as `(√(1 + x²))⁻¹`;
we restate it in the fractional form `1/√(1 + x²)` that matches the integrand. -/
theorem hasDerivAt_arsinh' (x : ℝ) :
    HasDerivAt arsinh (1 / Real.sqrt (1 + x ^ 2)) x := by
  simpa [one_div] using Real.hasDerivAt_arsinh x

/-- The `deriv` form of the antiderivative fact: `(arsinh)' x = 1/√(1 + x²)`. -/
theorem deriv_arsinh_eq (x : ℝ) :
    deriv arsinh x = 1 / Real.sqrt (1 + x ^ 2) :=
  (hasDerivAt_arsinh' x).deriv

/-- The integrand `x ↦ 1/√(1 + x²)` is continuous on all of `ℝ`. -/
theorem continuous_integrand :
    Continuous fun x : ℝ => 1 / Real.sqrt (1 + x ^ 2) :=
  continuous_const.div
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
    (fun x => ne_of_gt (sqrt_one_add_sq_pos x))

/-- Consequently the integrand is interval-integrable on every `[a, b]`. -/
theorem intervalIntegrable_integrand (a b : ℝ) :
    IntervalIntegrable (fun x => 1 / Real.sqrt (1 + x ^ 2)) volume a b :=
  continuous_integrand.intervalIntegrable a b

/-- **Fundamental Theorem of Calculus for `arsinh`.**
`∫_a^b 1/√(1 + t²) dt = arsinh b − arsinh a`.

This is the definite-integral incarnation of the antiderivative `arsinh`, and
the precise meaning of "`∫ 1/√(1 + x²) dx = arsinh x + C`". -/
theorem integral_one_div_sqrt_one_add_sq (a b : ℝ) :
    ∫ x in a..b, 1 / Real.sqrt (1 + x ^ 2) = arsinh b - arsinh a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _; exact hasDerivAt_arsinh' x
  · exact intervalIntegrable_integrand a b

/-- **Logarithmic closed form of the integral.**
`∫_a^b 1/√(1 + t²) dt = log(b + √(1 + b²)) − log(a + √(1 + a²))`,
obtained by unfolding `arsinh` to its parent logarithmic form. -/
theorem integral_eq_log_sub_log (a b : ℝ) :
    ∫ x in a..b, 1 / Real.sqrt (1 + x ^ 2) =
      Real.log (b + Real.sqrt (1 + b ^ 2)) -
        Real.log (a + Real.sqrt (1 + a ^ 2)) := by
  rw [integral_one_div_sqrt_one_add_sq]
  rfl

/-- **Normalised antiderivative (`C = 0`).** Anchoring the lower limit at `0`,
where `arsinh 0 = 0`, gives `∫_0^b 1/√(1 + t²) dt = arsinh b`. -/
theorem integral_zero_to (b : ℝ) :
    ∫ x in (0 : ℝ)..b, 1 / Real.sqrt (1 + x ^ 2) = arsinh b := by
  rw [integral_one_div_sqrt_one_add_sq, arsinh_zero, sub_zero]

/-- The normalised integral in logarithmic closed form:
`∫_0^b 1/√(1 + t²) dt = log(b + √(1 + b²))`. -/
theorem integral_zero_to_log (b : ℝ) :
    ∫ x in (0 : ℝ)..b, 1 / Real.sqrt (1 + x ^ 2) =
      Real.log (b + Real.sqrt (1 + b ^ 2)) := by
  rw [integral_zero_to]
  rfl

/-- **Even integrand, symmetric interval.** Since the integrand is even and
`arsinh` is odd, `∫_{-a}^a 1/√(1 + t²) dt = 2·arsinh a`. -/
theorem integral_symmetric (a : ℝ) :
    ∫ x in (-a)..a, 1 / Real.sqrt (1 + x ^ 2) = 2 * arsinh a := by
  rw [integral_one_div_sqrt_one_add_sq, Real.arsinh_neg]
  ring

/-- Concrete evaluation `∫_0^{3/4} 1/√(1 + t²) dt = log 2`, since
`arsinh (3/4) = log 2` (the parent's value `√(1 + (3/4)²) = 5/4`). -/
theorem integral_zero_to_three_quarters :
    ∫ x in (0 : ℝ)..(3 / 4), 1 / Real.sqrt (1 + x ^ 2) = Real.log 2 := by
  rw [integral_zero_to]
  have h : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show (1 + (3 / 4 : ℝ) ^ 2) = (5 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.log ((3 / 4 : ℝ) + Real.sqrt (1 + (3 / 4 : ℝ) ^ 2)) = Real.log 2
  rw [h, show (3 / 4 + 5 / 4 : ℝ) = 2 by norm_num]

/-- Concrete evaluation `∫_0^{4/3} 1/√(1 + t²) dt = log 3`, since
`arsinh (4/3) = log 3` (the parent's value `√(1 + (4/3)²) = 5/3`). -/
theorem integral_zero_to_four_thirds :
    ∫ x in (0 : ℝ)..(4 / 3), 1 / Real.sqrt (1 + x ^ 2) = Real.log 3 := by
  rw [integral_zero_to]
  have h : Real.sqrt (1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 + (4 / 3 : ℝ) ^ 2) = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.log ((4 / 3 : ℝ) + Real.sqrt (1 + (4 / 3 : ℝ) ^ 2)) = Real.log 3
  rw [h, show (4 / 3 + 5 / 3 : ℝ) = 3 by norm_num]

end ArsinhLogFormulaOQ01OQ01
