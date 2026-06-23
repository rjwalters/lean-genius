import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Squared Complex Gaussian Integral (∫ e^{-b x²})² = π/b

## Open Question (area-of-circle-oq-07-oq-04)
For the complex-parameter Gaussian of the sibling `area-of-circle-oq-07-oq-01`,
∫_ℝ e^{-b x²} dx = (π/b)^{1/2}, formalize that its **square** is the clean
rational value
    (∫_ℝ e^{-b x²} dx)² = π / b
for every `b : ℂ` with `0 < re b`.

## Answer: YES.

Squaring removes the branch-cut subtlety of the principal `(1/2)`-power: while
the integral itself is `(π/b)^{1/2}`, its square collapses to `π/b` directly.
Over the right half-plane `{b : ℂ | re b > 0}` the base `π/b` is nonzero, so
`(π/b)^{1/2} · (π/b)^{1/2} = (π/b)^{1/2 + 1/2} = (π/b)^1 = π/b`
by `Complex.cpow_add`.  This is the complex-parameter form of the classical
two-dimensional trick `(∫ e^{-x²})² = ∫∫ e^{-(x²+y²)} = π` that underlies the
area-of-a-circle / Gaussian computation in the parent `area-of-circle-oq-07`.

The parent's real value `(∫_ℝ e^{-x²})² = π` is the `b = 1` specialization,
recorded as `gaussian_integral_sq_eq_pi`: the integrand is real-valued, so the
real integral is the pushforward of the complex one through `ℂ`
(`integral_complex_ofReal`), and `π / 1 = π`.

No new axioms: a routine squaring and casting of existing Mathlib results.
-/

open Real Complex MeasureTheory

/-- **The squared complex Gaussian integral.** For every complex `b` with
positive real part, `(∫_ℝ e^{-b x²} dx)² = π/b`.  Squaring the principal
`(1/2)`-power value `(π/b)^{1/2}` of Mathlib's `integral_gaussian_complex`
returns the clean rational value `π/b`, the complex-parameter form of the
classical `(∫ e^{-x²})² = π`. -/
theorem gaussian_integral_complex_sq {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2)) ^ 2 = (↑π : ℂ) / b := by
  have hb_ne : b ≠ 0 := by rintro rfl; simp at hb
  have hz : ((↑π : ℂ) / b) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hb_ne
  rw [integral_gaussian_complex hb, pow_two, ← Complex.cpow_add _ _ hz]
  norm_num

/-- The real parent value `(∫_ℝ e^{-x²} dx)² = π` is the `b = 1` case: the
integrand is real-valued, so the real integral pushes forward to the complex
Gaussian, and `π / 1 = π`. -/
theorem gaussian_integral_sq_eq_pi :
    (∫ x : ℝ, Real.exp (-x ^ 2)) ^ 2 = Real.pi := by
  have hc := gaussian_integral_complex_sq (b := 1) (by simp)
  have hLcast : ((∫ x : ℝ, Real.exp (-x ^ 2) : ℝ) : ℂ)
      = ∫ x : ℝ, Complex.exp (-1 * (x : ℂ) ^ 2) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [div_one] at hc
  rw [← hLcast] at hc
  exact_mod_cast hc
