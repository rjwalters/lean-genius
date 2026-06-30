/-
# Affine arc length and the catenoid surface of revolution

Research: arsinh-log-formula-oq-01-oq-01-oq-01-oq-01
Parent:   arsinh-log-formula-oq-01-oq-01-oq-01 (catenary arc length and the
          antiderivative of `√(1 + t²)`)

The parent file ran the arc-length machinery on the conjugate integrand
`√(1 + t²)`, evaluating `∫_a^b √(1 + t²) dt` via the arsinh antiderivative and
collapsing the catenary integrand through `√(1 + sinh²x) = cosh x` to obtain the
catenary arc length `∫_0^b cosh x dx = sinh b`.

This child supplies the two pieces the parent left open in its open-question
list — the *affine* boundary case and the *surface of revolution* upgrade:

* `hasDerivAt_affine` / `line_arclength` — for a straight line `y = m·x + c`
  the arc-length integrand is the constant `√(1 + m²)`, so the arc length over
  `[a, b]` is `(b − a)·√(1 + m²)`.  This is the affine specialisation of the
  general smooth arc-length integral `∫ √(1 + f'²)` with `f'(t) = m`.

* `hasDerivAt_coshSqAntideriv` — the genuinely new antiderivative
  `d/dx [½(x + sinh x · cosh x)] = cosh²x`, built from the product rule on
  `sinh·cosh` and the Pythagorean identity `cosh²x = 1 + sinh²x`.  Mathlib
  supplies the `sinh`/`cosh` derivatives but no antiderivative for `cosh²`.
* `integral_cosh_sq_zero_to` — the FTC evaluation
  `∫_0^b cosh²x dx = ½(b + sinh b · cosh b)`.
* `catenoid_surface_area` — the headline geometric statement.  Revolving the
  catenary `y = cosh x` over `[0, b]` about the `x`-axis gives the *catenoid*,
  whose surface area `2π ∫_0^b cosh x · √(1 + sinh²x) dx` collapses (again via
  `√(1 + sinh²x) = cosh x`) to `2π ∫_0^b cosh²x dx = π (b + sinh b · cosh b)`.

All results are `0`-axiom and machine-checked.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ01OQ01OQ01

open Real intervalIntegral MeasureTheory

/-! ## The affine (straight-line) boundary case -/

/-- The affine map `x ↦ m·x + c` is differentiable with constant derivative `m`;
hence its arc-length integrand `√(1 + f'²)` is the constant `√(1 + m²)`. -/
theorem hasDerivAt_affine (m c t : ℝ) :
    HasDerivAt (fun x : ℝ => m * x + c) m t := by
  simpa using ((hasDerivAt_id t).const_mul m).add_const c

/-- **Affine arc length.** The arc length of the line `y = m·x + c` over `[a, b]`
is `(b − a)·√(1 + m²)`, because the arc-length integrand `√(1 + f'(t)²)` is the
constant `√(1 + m²)`. -/
theorem line_arclength (m a b : ℝ) :
    ∫ _t in a..b, Real.sqrt (1 + m ^ 2) = (b - a) * Real.sqrt (1 + m ^ 2) := by
  rw [intervalIntegral.integral_const, smul_eq_mul]

/-! ## The catenoid surface of revolution -/

/-- **Pythagorean simplification of the catenary integrand.**
`√(1 + sinh²x) = cosh x`, since `cosh²x = 1 + sinh²x` and `cosh x > 0`. -/
theorem sqrt_one_add_sinh_sq (x : ℝ) :
    Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
  have h : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
    have := Real.cosh_sq x
    linarith
  rw [h, Real.sqrt_sq (Real.cosh_pos x).le]

/-- **The new antiderivative.** `G(x) = ½(x + sinh x · cosh x)` is an
antiderivative of `cosh²x`:

`d/dx [½(x + sinh x · cosh x)] = cosh²x`.

Mathlib supplies the `sinh`/`cosh` derivatives but no antiderivative for the
`cosh²` integrand.  Differentiating the product gives
`(sinh·cosh)' = cosh²x + sinh²x`, and adding the `x` term and halving collapses
to `cosh²x` via `cosh²x = 1 + sinh²x`. -/
theorem hasDerivAt_coshSqAntideriv (x : ℝ) :
    HasDerivAt (fun u : ℝ => (u + Real.sinh u * Real.cosh u) / 2)
      (Real.cosh x ^ 2) x := by
  -- (sinh·cosh)' = cosh·cosh + sinh·sinh
  have hprod : HasDerivAt (fun u : ℝ => Real.sinh u * Real.cosh u)
      (Real.cosh x * Real.cosh x + Real.sinh x * Real.sinh x) x :=
    (Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_cosh x)
  have hsum := ((hasDerivAt_id x).add hprod).div_const 2
  convert hsum using 1
  -- value equality: cosh²x = (1 + (cosh·cosh + sinh·sinh))/2
  rw [← pow_two, ← pow_two]
  have := Real.cosh_sq x
  linarith

/-- The `cosh²` integrand is continuous, hence interval-integrable. -/
theorem continuous_cosh_sq : Continuous (fun x : ℝ => Real.cosh x ^ 2) :=
  Real.continuous_cosh.pow 2

/-- **FTC for `cosh²`.** `∫_0^b cosh²x dx = ½(b + sinh b · cosh b)`. -/
theorem integral_cosh_sq_zero_to (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.cosh x ^ 2 = (b + Real.sinh b * Real.cosh b) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_coshSqAntideriv x)
        (continuous_cosh_sq.intervalIntegrable 0 b)]
  simp [Real.sinh_zero, Real.cosh_zero]

/-- **Catenoid surface area.** Revolving the catenary `y = cosh x` over `[0, b]`
about the `x`-axis produces the catenoid, whose surface area is

`2π ∫_0^b cosh x · √(1 + sinh²x) dx = π (b + sinh b · cosh b)`.

The surface-of-revolution integrand `2π · y · √(1 + y'²)` simplifies through
`√(1 + sinh²x) = cosh x` to `2π · cosh²x`, so the area collapses to
`2π ∫_0^b cosh²x dx`. -/
theorem catenoid_surface_area (b : ℝ) :
    2 * Real.pi * ∫ x in (0 : ℝ)..b, Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2)
      = Real.pi * (b + Real.sinh b * Real.cosh b) := by
  have heq : (fun x : ℝ => Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2))
      = fun x : ℝ => Real.cosh x ^ 2 := by
    funext x
    rw [sqrt_one_add_sinh_sq, ← pow_two]
  rw [heq, integral_cosh_sq_zero_to]
  ring

/-- Concrete value: the catenoid over `[0, 1]` has surface area
`π (1 + sinh 1 · cosh 1)`. -/
theorem catenoid_surface_area_zero_to_one :
    2 * Real.pi * ∫ x in (0 : ℝ)..1, Real.cosh x * Real.sqrt (1 + Real.sinh x ^ 2)
      = Real.pi * (1 + Real.sinh 1 * Real.cosh 1) := by
  simpa using catenoid_surface_area 1

end ArsinhLogFormulaOQ01OQ01OQ01OQ01
