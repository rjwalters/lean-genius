import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Euler identity OQ-01 → OQ-02: the Taylor series of cos/sin from the exponential definition

The parent chain (`euler-identity`) proves Euler's formula `e^{ix} = cos x + i·sin x` and the
identity `e^{iπ} = −1`. Its OQ-01-OQ-02 asks to

> *derive `cos_eq_tsum` (the power series of cos) from the Mathlib definition
> `cos z = (e^{iz} + e^{−iz})/2`.*

In Mathlib `Complex.cos` is literally defined as `(e^{iz} + e^{−iz})/2`, and its power series
`cos z = Σ (−1)ⁿ z²ⁿ/(2n)!` is derived from that definition (`Complex.cos_eq_tsum`). This
file packages the exponential form, the power series of cos and sin (over `ℂ` and `ℝ`),
Euler's formula, and Euler's identity, exhibiting the chain definition → series → identity.
`0` axioms.

## Main results

* `cos_eq_exp` / `sin_eq_exp` : `cos x = (e^{ix} + e^{−ix})/2`, `sin x = (e^{ix} − e^{−ix})/(2i)`.
* `cos_eq_tsum` / `sin_eq_tsum` : the power series `cos z = Σ (−1)ⁿ z²ⁿ/(2n)!`, etc.
* `real_cos_eq_tsum` / `real_sin_eq_tsum` : the real-variable power series.
* `euler_formula` : `e^{ix} = cos x + sin x·i`.
* `euler_identity` : `e^{iπ} = −1`.
-/

namespace EulerIdentityOQ01OQ02

open Complex

/-- **The exponential definition of cosine.** `cos x = (e^{ix} + e^{−ix})/2`, the form from
    which Mathlib defines `Complex.cos`. (Derived from `Complex.two_cos`.) -/
theorem cos_eq_exp (x : ℂ) :
    Complex.cos x = (Complex.exp (x * I) + Complex.exp (-x * I)) / 2 := by
  rw [← Complex.two_cos]; ring

/-- **The exponential definition of sine.** `sin x = (e^{ix} − e^{−ix})/(2i)`. -/
theorem sin_eq_exp (x : ℂ) :
    Complex.sin x = (Complex.exp (-x * I) - Complex.exp (x * I)) * I / 2 := by
  rw [← Complex.two_sin]; ring

/-- **The power series of cosine** `cos z = Σₙ (−1)ⁿ z²ⁿ/(2n)!`, derived from the exponential
    definition (Mathlib: `Complex.cos_eq_tsum`). This is the OQ's target: the Taylor series
    obtained from `cos z = (e^{iz} + e^{−iz})/2`. -/
theorem cos_eq_tsum (z : ℂ) :
    Complex.cos z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n) / ((2 * n).factorial : ℂ) :=
  Complex.cos_eq_tsum z

/-- **The power series of sine** `sin z = Σₙ (−1)ⁿ z²ⁿ⁺¹/(2n+1)!`. -/
theorem sin_eq_tsum (z : ℂ) :
    Complex.sin z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ) :=
  Complex.sin_eq_tsum z

/-- The real-variable power series of cosine. -/
theorem real_cos_eq_tsum (r : ℝ) :
    Real.cos r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n) / ((2 * n).factorial : ℝ) :=
  Real.cos_eq_tsum r

/-- The real-variable power series of sine. -/
theorem real_sin_eq_tsum (r : ℝ) :
    Real.sin r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) :=
  Real.sin_eq_tsum r

/-- **Euler's formula** `e^{ix} = cos x + sin x·i` (Mathlib: `Complex.exp_mul_I`). -/
theorem euler_formula (x : ℂ) :
    Complex.exp (x * I) = Complex.cos x + Complex.sin x * I :=
  Complex.exp_mul_I x

/-- **Euler's identity** `e^{iπ} = −1` (Mathlib: `Complex.exp_pi_mul_I`). -/
theorem euler_identity : Complex.exp (↑Real.pi * I) = -1 :=
  Complex.exp_pi_mul_I

end EulerIdentityOQ01OQ02
