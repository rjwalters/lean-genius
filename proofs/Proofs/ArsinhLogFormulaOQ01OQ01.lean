import Mathlib

/-!
# The arsinh antiderivative: ∫ 1/√(1 + x²) dx = arsinh x

The parent entry (`ArsinhLogFormulaOQ01`) gives the inverse hyperbolic sine its
closed logarithmic form `arsinh x = log (x + √(1 + x²))` and its addition calculus,
and lists as its first open question:

> Establish `∫ 1/√(1 + x²) dx = arsinh x + C` from `hasDerivAt_arsinh`.

This file answers it. Mathlib records the pointwise derivative
`Real.hasDerivAt_arsinh : HasDerivAt arsinh (√(1 + x²))⁻¹ x` and the continuity of
`arsinh`, but it does **not** record the resulting **antiderivative / definite
integral** identity. Turning the derivative fact into an integral via the
Fundamental Theorem of Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`)
gives, for all real `a b`,

  `∫ x in a..b, 1/√(1 + x²) = arsinh b − arsinh a`,

the precise sense in which `arsinh` is *the* antiderivative of `1/√(1 + x²)`
(the constant `C` is fixed by `arsinh 0 = 0`, recovering
`∫ t in 0..x, 1/√(1 + t²) = arsinh x`). The integrand is continuous everywhere —
`1 + x² ≥ 1 > 0`, so `√(1 + x²) > 0` and no singularity arises — which is exactly
what makes the FTC apply on every interval, in contrast to `1/√(1 − x²)`
(the `arcsin` integrand) whose domain is bounded.

Composing with the parent's logarithmic form turns the definite integral into a
difference of logarithms, and composing with the parent's concrete values
`arsinh (3/4) = log 2`, `arsinh (4/3) = log 3` evaluates two definite integrals in
closed form. Everything is machine-checked with no axioms.
-/

namespace ArsinhLogFormulaOQ01OQ01

open Real

/-- **Closed logarithmic form of `arsinh`** (the Mathlib definition, named for
reference): `arsinh x = log (x + √(1 + x²))`. -/
theorem arsinh_eq_log (x : ℝ) : arsinh x = Real.log (x + Real.sqrt (1 + x ^ 2)) := rfl

/-! ## The derivative and the integrand -/

/-- **Pointwise derivative of `arsinh`, in `1 / √` form.** A restatement of
Mathlib's `Real.hasDerivAt_arsinh` with the derivative written as
`1 / √(1 + x²)` rather than `(√(1 + x²))⁻¹`. -/
theorem hasDerivAt_arsinh' (x : ℝ) :
    HasDerivAt arsinh (1 / Real.sqrt (1 + x ^ 2)) x := by
  simpa [one_div] using Real.hasDerivAt_arsinh x

/-- The Fréchet derivative of `arsinh` as an ordinary `deriv`. -/
theorem deriv_arsinh (x : ℝ) : deriv arsinh x = 1 / Real.sqrt (1 + x ^ 2) :=
  (hasDerivAt_arsinh' x).deriv

/-- The integrand `1 / √(1 + x²)` is **continuous on all of `ℝ`**: the radicand
`1 + x²` is bounded below by `1`, so `√(1 + x²) > 0` everywhere and the quotient
never meets a singularity. -/
theorem continuous_integrand :
    Continuous (fun x : ℝ => 1 / Real.sqrt (1 + x ^ 2)) := by
  apply Continuous.div continuous_const
  · exact Real.continuous_sqrt.comp (by fun_prop)
  · intro x
    have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
    exact ne_of_gt (Real.sqrt_pos.mpr hx)

/-- The integrand is interval-integrable on every interval (continuous ⇒ integrable). -/
theorem intervalIntegrable_integrand (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1 + x ^ 2)) MeasureTheory.volume a b :=
  continuous_integrand.intervalIntegrable a b

/-! ## The antiderivative (Fundamental Theorem of Calculus) -/

/-- **Main result.** `arsinh` is the antiderivative of `1 / √(1 + x²)`:
for all real `a, b`,
`∫ x in a..b, 1 / √(1 + x²) = arsinh b − arsinh a`. -/
theorem integral_oneDivSqrt_eq_arsinh (a b : ℝ) :
    ∫ x in a..b, 1 / Real.sqrt (1 + x ^ 2) = arsinh b - arsinh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_arsinh' x) (intervalIntegrable_integrand a b)

/-- **Normalized antiderivative.** Fixing the constant by `arsinh 0 = 0`:
`∫ t in 0..x, 1 / √(1 + t²) = arsinh x`. This is the `+ C` of the open question
with `C = 0`. -/
theorem integral_zero_to_eq_arsinh (x : ℝ) :
    ∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2) = arsinh x := by
  rw [integral_oneDivSqrt_eq_arsinh, Real.arsinh_zero, sub_zero]

/-- The integrand is **even**, so the integral over a symmetric interval doubles:
`∫ t in (−x)..x, 1 / √(1 + t²) = 2 · arsinh x` (using `arsinh (−x) = −arsinh x`). -/
theorem integral_symmetric (x : ℝ) :
    ∫ t in (-x)..x, 1 / Real.sqrt (1 + t ^ 2) = 2 * arsinh x := by
  rw [integral_oneDivSqrt_eq_arsinh, Real.arsinh_neg]; ring

/-! ## Logarithmic form -/

/-- The definite integral written via the parent's closed logarithmic form
`arsinh x = log (x + √(1 + x²))`:
`∫ x in a..b, 1/√(1 + x²) = log (b + √(1 + b²)) − log (a + √(1 + a²))`. -/
theorem integral_oneDivSqrt_eq_log (a b : ℝ) :
    ∫ x in a..b, 1 / Real.sqrt (1 + x ^ 2)
      = Real.log (b + Real.sqrt (1 + b ^ 2)) - Real.log (a + Real.sqrt (1 + a ^ 2)) := by
  rw [integral_oneDivSqrt_eq_arsinh, arsinh_eq_log, arsinh_eq_log]

/-! ## Concrete closed-form values

Composing the normalized antiderivative with the closed-form evaluations
`arsinh (3/4) = log 2` and `arsinh (4/3) = log 3` (each via `√(1 + (3/4)²) = 5/4`,
`√(1 + (4/3)²) = 5/3`). -/

/-- `∫ t in 0..(3/4), 1 / √(1 + t²) = log 2`. -/
theorem integral_zero_to_three_quarters :
    ∫ t in (0 : ℝ)..(3 / 4), 1 / Real.sqrt (1 + t ^ 2) = Real.log 2 := by
  rw [integral_zero_to_eq_arsinh, arsinh_eq_log]
  have h : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show (1 + (3 / 4 : ℝ) ^ 2) = (5 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h, show (3 / 4 + 5 / 4 : ℝ) = 2 by norm_num]

/-- `∫ t in 0..(4/3), 1 / √(1 + t²) = log 3`. -/
theorem integral_zero_to_four_thirds :
    ∫ t in (0 : ℝ)..(4 / 3), 1 / Real.sqrt (1 + t ^ 2) = Real.log 3 := by
  rw [integral_zero_to_eq_arsinh, arsinh_eq_log]
  have h : Real.sqrt (1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 + (4 / 3 : ℝ) ^ 2) = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h, show (4 / 3 + 5 / 3 : ℝ) = 3 by norm_num]

end ArsinhLogFormulaOQ01OQ01
