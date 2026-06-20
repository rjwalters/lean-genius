import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Complex-Parameter Gaussian Integral

## Open Question (area-of-circle-oq-07-oq-01)
"Does the Gaussian integral formula survive when the rate parameter `b` is taken
to be a *complex* number rather than a positive real?"

$$ \int_{-\infty}^{\infty} e^{-b x^2}\, dx = \left(\tfrac{\pi}{b}\right)^{1/2},
   \qquad \operatorname{Re} b > 0. $$

## Answer: YES, for every `b : ℂ` with `Re b > 0`.

The parent entry `area-of-circle-oq-07` evaluates the real Gaussian
`∫_ℝ e^{-x²} = √π`, a `b = 1` slice of the real parametrized integral
`integral_gaussian`.  Mathlib goes further: `integral_gaussian_complex` proves
the same closed form for an arbitrary **complex** rate `b` with positive real
part, the value being the principal square root `(π/b)^{1/2}` taken with
`Complex.cpow`.  This is a genuine generalization — it covers the oscillatory
Fresnel-type regime that appears as `Re b → 0⁺`, where the integrand stops being
a decaying bell curve and starts to spiral.

To anchor the complex statement against the parent we add the
**real-parameter bridge** `complex_gaussian_integral_ofReal`: for a positive real
`b`, the complex value `(π/b)^{1/2}` is just the real square root `√(π/b)` cast
into `ℂ`.  The proof routes through `Complex.ofReal_exp` and `integral_ofReal`,
pushing the whole computation back onto the real `integral_gaussian`, and the
`b = 1` corollary recovers the parent's `√π` inside `ℂ`.

No new axioms: every step is a routine consequence of existing Mathlib results.
-/

open Real MeasureTheory

/-- **The complex-parameter Gaussian integral.** For every complex `b` with
positive real part, `∫_ℝ e^{-b x²} dx = (π/b)^{1/2}` (principal complex root). -/
theorem complex_gaussian_integral {b : ℂ} (hb : 0 < b.re) :
    ∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2) = ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) :=
  integral_gaussian_complex hb

/-- **Real-parameter bridge.** When the rate `b` is a positive *real* number, the
complex Gaussian value is the real square root `√(π/b)` cast into `ℂ`.  The proof
pushes the integral back onto the real `integral_gaussian` via `Complex.ofReal_exp`
and `integral_ofReal`. -/
theorem complex_gaussian_integral_ofReal {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) = (Real.sqrt (Real.pi / b) : ℂ) := by
  have hb' : 0 < ((b : ℂ)).re := by simpa using hb
  rw [integral_gaussian_complex hb', Real.sqrt_eq_rpow,
    Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ Real.pi / b), Complex.ofReal_div]
  norm_num

/-- **Recovering the parent inside ℂ.** At `b = 1` the complex Gaussian integral
of `e^{-x²}` is `√π` (cast into `ℂ`) — the complexified form of the parent entry
`area-of-circle-oq-07`. -/
theorem complex_gaussian_integral_one :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2) = (Real.sqrt Real.pi : ℂ) := by
  have h := complex_gaussian_integral_ofReal (b := 1) one_pos
  simpa using h
