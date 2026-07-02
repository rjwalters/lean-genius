/-
# Catenary arc length via the `arsinh` substitution: the logarithmic closed
# form and the catenoid surface area

Research: arsinh-log-formula-oq-01-oq-01-oq-02
Parent:   arsinh-log-formula-oq-01-oq-01 (antiderivative of `1/√(1 + t²)` is `arsinh`)

The sibling `arsinh-log-formula-oq-01-oq-01-oq-01` established the arc-length
closed form in **`arsinh`** notation:
`∫_0^b √(1 + t²) dt = ½(b·√(1+b²) + arsinh b)` and the catenary length
`∫_0^b √(1 + sinh²x) dx = sinh b`.

This file supplies the two genuinely new companions on the same lineage — the
whole point of the `arsinh`-**log** formula being the passage to logarithms, and
the natural next geometric quantity being the surface of revolution:

* `integral_sqrt_one_add_sq_log` — the **purely logarithmic** closed form
  `∫_0^b √(1 + t²) dt = ½(b·√(1+b²) + log(b + √(1+b²)))`, obtained by unfolding
  `arsinh` to its defining logarithm (`arsinh x = log(x + √(1+x²))`).  This is the
  form in which the catenary arc length is classically tabulated.
* `integral_sqrt_one_add_sq_zero_to_one_log` — the concrete value
  `∫_0^1 √(1 + t²) dt = ½(√2 + log(1 + √2))`.
* `hasDerivAt_coshSqAntideriv` — the new antiderivative
  `d/dx [½(x + sinh x·cosh x)] = cosh²x` (product rule on `sinh·cosh`, collapsed
  via `cosh²x = 1 + sinh²x`).
* `integral_cosh_sq_zero_to` — `∫_0^b cosh²x dx = ½(b + sinh b·cosh b)`.
* `catenoid_surface_area` — the headline: the lateral surface area of the
  **catenoid** obtained by revolving the catenary `y = cosh x`, `0 ≤ x ≤ b`,
  about the axis is
  `∫_0^b 2π·cosh x·√(1 + sinh²x) dx = π(b + sinh b·cosh b)`,
  since the arc-length element `√(1 + sinh²x) = cosh x` turns the integrand into
  `2π·cosh²x`.
* `catenoid_surface_area_zero_to_one` — the concrete value
  `π(1 + sinh 1·cosh 1)`.

All results are `0`-axiom and machine-checked.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ01OQ02

open Real intervalIntegral MeasureTheory

/-! ## The `√(1 + t²)` antiderivative and its logarithmic evaluation -/

/-- The radicand `1 + t²` is strictly positive, hence `√(1 + t²) > 0`. -/
theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

/-- The square of `√(1 + t²)` is `1 + t²` (the radicand is nonnegative). -/
theorem sq_sqrt_one_add_sq (t : ℝ) : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `F(t) = ½(t·√(1 + t²) + arsinh t)` is an antiderivative of `√(1 + t²)`.
Mathlib provides `Real.hasDerivAt_arsinh` but no antiderivative for the conjugate
integrand `√(1 + t²)`; we build it from the product rule, the chain rule for `√`,
and the `arsinh` derivative.  The algebra collapses because
`(t² + 1)/√(1+t²) = √(1+t²)`, doubling the leading term. -/
theorem hasDerivAt_sqrtAntideriv (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x * Real.sqrt (1 + x ^ 2) + Real.arsinh x) / 2)
      (Real.sqrt (1 + t ^ 2)) t := by
  have h1pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hne : (1 + t ^ 2) ≠ 0 := ne_of_gt h1pos
  have hquad : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (1 : ℝ)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (2 * t / (2 * Real.sqrt (1 + t ^ 2))) t := hquad.sqrt hne
  have hprod : HasDerivAt (fun x : ℝ => x * Real.sqrt (1 + x ^ 2))
      (1 * Real.sqrt (1 + t ^ 2) + t * (2 * t / (2 * Real.sqrt (1 + t ^ 2)))) t :=
    (hasDerivAt_id t).mul hsqrt
  have hsum := (hprod.add (Real.hasDerivAt_arsinh t)).div_const 2
  convert hsum using 1
  have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := sq_sqrt_one_add_sq t
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := sqrt_one_add_sq_pos t
  field_simp
  nlinarith [hs, hpos]

/-- The integrand `t ↦ √(1 + t²)` is interval-integrable on every `[a, b]`. -/
theorem intervalIntegrable_sqrt_integrand (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (1 + t ^ 2)) volume a b := by
  apply Continuous.intervalIntegrable; fun_prop

/-- FTC for `√(1 + t²)` over `[0, b]` in `arsinh` form:
`∫_0^b √(1 + t²) dt = ½(b·√(1+b²) + arsinh b)`. -/
theorem integral_sqrt_one_add_sq_zero_to (b : ℝ) :
    ∫ t in (0 : ℝ)..b, Real.sqrt (1 + t ^ 2)
      = (b * Real.sqrt (1 + b ^ 2) + Real.arsinh b) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_sqrtAntideriv t)
        (intervalIntegrable_sqrt_integrand 0 b)]
  simp [Real.arsinh_zero]

/-- **Logarithmic closed form.** Unfolding `arsinh x = log(x + √(1+x²))` gives the
classical tabulated form of the catenary arc length:
`∫_0^b √(1 + t²) dt = ½(b·√(1+b²) + log(b + √(1+b²)))`. -/
theorem integral_sqrt_one_add_sq_log (b : ℝ) :
    ∫ t in (0 : ℝ)..b, Real.sqrt (1 + t ^ 2)
      = (b * Real.sqrt (1 + b ^ 2) + Real.log (b + Real.sqrt (1 + b ^ 2))) / 2 := by
  rw [integral_sqrt_one_add_sq_zero_to]
  rfl

/-- Concrete value in logarithmic form:
`∫_0^1 √(1 + t²) dt = ½(√2 + log(1 + √2))`. -/
theorem integral_sqrt_one_add_sq_zero_to_one_log :
    ∫ t in (0 : ℝ)..1, Real.sqrt (1 + t ^ 2)
      = (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) / 2 := by
  rw [integral_sqrt_one_add_sq_log]
  norm_num

/-! ## The catenoid surface area -/

/-- **Pythagorean simplification of the catenary arc-length element.**
`√(1 + sinh²x) = cosh x`, since `cosh²x = 1 + sinh²x` and `cosh x > 0`. -/
theorem sqrt_one_add_sinh_sq (x : ℝ) :
    Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
  have h : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
    have := Real.cosh_sq x; linarith
  rw [h, Real.sqrt_sq (Real.cosh_pos x).le]

/-- **New antiderivative for `cosh²`.** `G(x) = ½(x + sinh x·cosh x)` satisfies
`G'(x) = cosh²x`.  The product rule gives `(sinh·cosh)' = cosh² + sinh²`, and
`cosh²x = 1 + sinh²x` collapses `½(1 + cosh² + sinh²) = cosh²`. -/
theorem hasDerivAt_coshSqAntideriv (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x + Real.sinh x * Real.cosh x) / 2)
      (Real.cosh t ^ 2) t := by
  have hprod : HasDerivAt (fun x : ℝ => Real.sinh x * Real.cosh x)
      (Real.cosh t * Real.cosh t + Real.sinh t * Real.sinh t) t :=
    (Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)
  have hsum := ((hasDerivAt_id t).add hprod).div_const 2
  convert hsum using 1
  have := Real.cosh_sq t
  nlinarith [this]

/-- The integrand `x ↦ cosh²x` is interval-integrable on every `[a, b]`. -/
theorem intervalIntegrable_cosh_sq (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cosh x ^ 2) volume a b := by
  apply Continuous.intervalIntegrable; fun_prop

/-- `∫_0^b cosh²x dx = ½(b + sinh b·cosh b)`. -/
theorem integral_cosh_sq_zero_to (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.cosh x ^ 2 = (b + Real.sinh b * Real.cosh b) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_coshSqAntideriv x)
        (intervalIntegrable_cosh_sq 0 b)]
  simp [Real.sinh_zero]

/-- **Catenoid surface area.** Revolving the catenary `y = cosh x`, `0 ≤ x ≤ b`,
about the axis produces a catenoid of lateral surface area

`∫_0^b 2π·cosh x·√(1 + sinh²x) dx = π(b + sinh b·cosh b)`.

The arc-length element `√(1 + (cosh)'²) = √(1 + sinh²x) = cosh x` turns the
Pappus integrand `2π·y·ds` into `2π·cosh²x`, whose antiderivative is
`π(x + sinh x·cosh x)`. -/
theorem catenoid_surface_area (b : ℝ) :
    ∫ x in (0 : ℝ)..b, 2 * Real.pi * Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2)
      = Real.pi * (b + Real.sinh b * Real.cosh b) := by
  have h1 : ∀ x : ℝ,
      2 * Real.pi * Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2)
        = (2 * Real.pi) * Real.cosh x ^ 2 := by
    intro x; rw [sqrt_one_add_sinh_sq]; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, integral_cosh_sq_zero_to]
  ring

/-- Concrete value: the catenoid over `[0, 1]` has surface area
`π(1 + sinh 1·cosh 1)`. -/
theorem catenoid_surface_area_zero_to_one :
    ∫ x in (0 : ℝ)..1, 2 * Real.pi * Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2)
      = Real.pi * (1 + Real.sinh 1 * Real.cosh 1) := by
  rw [catenoid_surface_area]

end ArsinhLogFormulaOQ01OQ01OQ02
