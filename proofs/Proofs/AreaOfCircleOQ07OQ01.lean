import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Complex Gaussian Integral ∫ e^{-b x²} = (π/b)^{1/2}

## Open Question (area-of-circle-oq-07-oq-01)
Extend the real Gaussian integral ∫_ℝ e^{-x²} dx = √π (the parent
`area-of-circle-oq-07`, the `b = 1` case) to the complex-parameter Gaussian
∫_ℝ e^{-b x²} dx = (π/b)^{1/2} for any `b : ℂ` with `0 < re b`.

## Answer: YES — Mathlib's `integral_gaussian_complex` evaluates it for every such b.

This is a genuine generalization of the parent to the full complex right
half-plane `{b : ℂ | re b > 0}`, the analytic continuation that underlies the
Fresnel-type oscillatory integrals reached as `re b → 0⁺`.  Unlike the real
case, the value is a complex principal `(1/2)`-power `(π/b)^{1/2}` rather than a
real square root.

The parent's real result `∫_ℝ e^{-x²} dx = √π` is recovered as the `b = 1`
specialization: the integrand is real-valued, so the real integral is the
pushforward of the complex one through `ℂ` (`integral_complex_ofReal`), and the
principal power `(π/1)^{1/2}` collapses to `(√π : ℂ)` via `Complex.ofReal_cpow`
and `Real.sqrt_eq_rpow`.  The bridge theorem
`gaussian_integral_eq_sqrt_pi_via_complex` records this recovery explicitly.

No new axioms: a routine specialization and casting of existing Mathlib results.
-/

open Real Complex MeasureTheory

/-- **The complex Gaussian integral.** For every complex `b` with positive real
part, `∫_ℝ e^{-b x²} dx = (π/b)^{1/2}`.  A restatement of Mathlib's
`integral_gaussian_complex`, generalizing the real parent to the complex right
half-plane. -/
theorem gaussian_integral_complex {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2)) = (↑π / b) ^ (1 / 2 : ℂ) :=
  integral_gaussian_complex hb

/-- The real parent `√π` is the `b = 1` case of the complex Gaussian:
`∫_ℝ e^{-x²} dx = √π`, recovered by pushing the (real-valued) integral through
`ℂ` and identifying `(π/1)^{1/2}` with `(√π : ℂ)`. -/
theorem gaussian_integral_eq_sqrt_pi_via_complex :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  have hc := gaussian_integral_complex (b := 1) (by simp)
  have hLcast : ((∫ x : ℝ, Real.exp (-x ^ 2) : ℝ) : ℂ)
      = ∫ x : ℝ, Complex.exp (-1 * (x : ℂ) ^ 2) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hRcast : ((↑π : ℂ) / 1) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg]
    push_cast
    ring_nf
  rw [← hLcast, hRcast] at hc
  exact_mod_cast hc
