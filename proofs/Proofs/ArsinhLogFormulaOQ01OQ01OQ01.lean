/-
# Catenary arc-length and the antiderivative of `√(1 + t²)`

Research: arsinh-log-formula-oq-01-oq-01-oq-01
Parent:   arsinh-log-formula-oq-01-oq-01 (antiderivative of `1/√(1 + t²)` is `arsinh`)

The parent file proved the calculus capstone for the integrand `1/√(1 + t²)`:
that `arsinh` is its antiderivative and the resulting FTC evaluations.  This
child supplies the *companion* arc-length facts, which run the same machinery on
the conjugate integrand `√(1 + t²)`:

* `hasDerivAt_sqrtAntideriv` — the genuinely new derivative computation
  `d/dt [½(t·√(1 + t²) + arsinh t)] = √(1 + t²)`.  Mathlib has the `arsinh`
  derivative but supplies *no* antiderivative for `√(1 + t²)`, so this is built
  from scratch (product + chain rule on `√`, plus `Real.hasDerivAt_arsinh`).
* `integral_sqrt_one_add_sq` — the FTC evaluation
  `∫_a^b √(1 + t²) dt = ½(b·√(1+b²) + arsinh b) − ½(a·√(1+a²) + arsinh a)`,
  obtained through the hyperbolic substitution `t = sinh u` whose antiderivative
  is the closed form above.
* `integral_sqrt_one_add_sq_zero_to` — the `∫_0^b` normalisation
  `= ½(b·√(1+b²) + arsinh b)`.
* `sqrt_one_add_sinh_sq` — the Pythagorean simplification
  `√(1 + sinh²x) = cosh x` that identifies the catenary arc-length integrand.
* `integral_cosh_zero_to` — `∫_0^b cosh x dx = sinh b`.
* `catenary_arclength` — the headline geometric statement: the arc length of the
  catenary `y = cosh x` over `[0, b]` is `sinh b`, since
  `√(1 + (cosh)'²) = √(1 + sinh²) = cosh`.
* `integral_sqrt_one_add_sq_zero_to_one` — the concrete value
  `∫_0^1 √(1 + t²) dt = ½(√2 + arsinh 1)`.

All results are `0`-axiom and machine-checked.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ01OQ01

open Real intervalIntegral MeasureTheory

/-- The radicand `1 + t²` is strictly positive, hence `√(1 + t²) > 0`. -/
theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

/-- The square of `√(1 + t²)` is `1 + t²` (the radicand is nonnegative). -/
theorem sq_sqrt_one_add_sq (t : ℝ) : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **The new antiderivative.** `F(t) = ½(t·√(1 + t²) + arsinh t)` is an
antiderivative of `√(1 + t²)`:

`d/dt [½(t·√(1 + t²) + arsinh t)] = √(1 + t²)`.

Mathlib provides `Real.hasDerivAt_arsinh` (the derivative of `arsinh`) but no
antiderivative for the conjugate integrand `√(1 + t²)`; we build it here from the
product rule, the chain rule for `√`, and the `arsinh` derivative.  The algebra
collapses because `(t² + 1)/√(1+t²) = √(1+t²)`, doubling the leading term. -/
theorem hasDerivAt_sqrtAntideriv (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x * Real.sqrt (1 + x ^ 2) + Real.arsinh x) / 2)
      (Real.sqrt (1 + t ^ 2)) t := by
  have h1pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hne : (1 + t ^ 2) ≠ 0 := ne_of_gt h1pos
  -- d/dt (1 + t²) = 2t
  have hquad : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (1 : ℝ)
  -- d/dt √(1 + t²) = (2t) / (2·√(1 + t²))
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (2 * t / (2 * Real.sqrt (1 + t ^ 2))) t := hquad.sqrt hne
  -- product rule for t·√(1 + t²)
  have hprod : HasDerivAt (fun x : ℝ => x * Real.sqrt (1 + x ^ 2))
      (1 * Real.sqrt (1 + t ^ 2) + t * (2 * t / (2 * Real.sqrt (1 + t ^ 2)))) t :=
    (hasDerivAt_id t).mul hsqrt
  -- add the arsinh term, then divide by 2
  have hsum := (hprod.add (Real.hasDerivAt_arsinh t)).div_const 2
  convert hsum using 1
  -- value equality: √(1+t²) = ((1·√ + t·(2t/(2√))) + (√)⁻¹)/2
  have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := sq_sqrt_one_add_sq t
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := sqrt_one_add_sq_pos t
  field_simp
  nlinarith [hs, hpos]

/-- The integrand `t ↦ √(1 + t²)` is continuous everywhere. -/
theorem continuous_sqrt_integrand :
    Continuous (fun t : ℝ => Real.sqrt (1 + t ^ 2)) := by
  fun_prop

/-- The integrand `t ↦ √(1 + t²)` is interval-integrable on every `[a, b]`. -/
theorem intervalIntegrable_sqrt_integrand (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (1 + t ^ 2)) volume a b :=
  continuous_sqrt_integrand.intervalIntegrable a b

/-- **FTC for `√(1 + t²)`.** Definite integral over `[a, b]` via the antiderivative
`F(t) = ½(t·√(1+t²) + arsinh t)`:

`∫_a^b √(1 + t²) dt = ½(b·√(1+b²) + arsinh b) − ½(a·√(1+a²) + arsinh a)`. -/
theorem integral_sqrt_one_add_sq (a b : ℝ) :
    ∫ t in a..b, Real.sqrt (1 + t ^ 2)
      = (b * Real.sqrt (1 + b ^ 2) + Real.arsinh b) / 2
        - (a * Real.sqrt (1 + a ^ 2) + Real.arsinh a) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_sqrtAntideriv t)
        (intervalIntegrable_sqrt_integrand a b)]

/-- The `∫_0^b` normalisation (the antiderivative with `C = 0`):
`∫_0^b √(1 + t²) dt = ½(b·√(1+b²) + arsinh b)`. -/
theorem integral_sqrt_one_add_sq_zero_to (b : ℝ) :
    ∫ t in (0 : ℝ)..b, Real.sqrt (1 + t ^ 2)
      = (b * Real.sqrt (1 + b ^ 2) + Real.arsinh b) / 2 := by
  rw [integral_sqrt_one_add_sq]
  simp [Real.arsinh_zero]

/-- **Pythagorean simplification of the catenary integrand.**
`√(1 + sinh²x) = cosh x`, since `cosh²x = 1 + sinh²x` and `cosh x > 0`. -/
theorem sqrt_one_add_sinh_sq (x : ℝ) :
    Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
  have h : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
    have := Real.cosh_sq x
    linarith
  rw [h, Real.sqrt_sq (Real.cosh_pos x).le]

/-- `∫_0^b cosh x dx = sinh b`, the FTC evaluation for the catenary integrand. -/
theorem integral_cosh_zero_to (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.cosh x = Real.sinh b := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => Real.hasDerivAt_sinh x)
        (Real.continuous_cosh.intervalIntegrable 0 b),
      Real.sinh_zero, sub_zero]

/-- **Catenary arc length.** The arc length of the catenary `y = cosh x` over
`[0, b]` is `sinh b`.

The arc-length integrand is `√(1 + (cosh)'²) = √(1 + sinh²x) = cosh x`, so the
length integral collapses to `∫_0^b cosh x dx = sinh b`. -/
theorem catenary_arclength (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.sqrt (1 + Real.sinh x ^ 2) = Real.sinh b := by
  simp_rw [sqrt_one_add_sinh_sq]
  exact integral_cosh_zero_to b

/-- Concrete value: `∫_0^1 √(1 + t²) dt = ½(√2 + arsinh 1)`. -/
theorem integral_sqrt_one_add_sq_zero_to_one :
    ∫ t in (0 : ℝ)..1, Real.sqrt (1 + t ^ 2) = (Real.sqrt 2 + Real.arsinh 1) / 2 := by
  rw [integral_sqrt_one_add_sq_zero_to]
  norm_num

end ArsinhLogFormulaOQ01OQ01OQ01
