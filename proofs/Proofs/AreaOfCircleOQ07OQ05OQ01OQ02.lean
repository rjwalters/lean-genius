import Proofs.AreaOfCircleOQ07OQ05OQ01
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-
# The Scaled General Even Moment of the Gaussian  (area-of-circle-oq-07-oq-05-oq-01-oq-02)

## Open Question (area-of-circle-oq-07-oq-05-oq-01-oq-02)
"Generalize to the scaled Gaussian
`∫_ℝ x^{2n} e^{-a x²} dx = (2n-1)‼ · √(π/a) / (2a)^n`."

## Answer

For every `n : ℕ` and every `a > 0`,

  `∫_{-∞}^{∞} x^{2n} e^{-a x²} dx = (2n-1)‼ · √(π/a) / (2a)^n`.

The parent entry `area-of-circle-oq-07-oq-05-oq-01` evaluated the **unscaled**
even moment `∫ x^{2n} e^{-x²} = (2n-1)‼·√π/2^n` by an integration-by-parts
induction.  This entry lifts that single result to **all** scales `a > 0` by one
linear change of variables, with no further analysis.

Write `s = √a` (so `s > 0` and `s² = a`).  Applying Mathlib's dilation rule for
real integrals (`integral_comp_mul_left`) to the unscaled integrand
`g y = y^{2n} e^{-y²}` gives

  `∫_x g(s·x) = |s⁻¹| · ∫_y g y`.

The left side is `aⁿ · ∫_x x^{2n} e^{-a x²}` (because `(s·x)^{2n} = aⁿ x^{2n}` and
`(s·x)² = a x²`), and the right side is `s⁻¹ · (2n-1)‼·√π/2^n` by the parent
moment.  Solving for the scaled integral and simplifying
`√(π/a) = √π / √a` and `(2a)^n = 2^n aⁿ` produces the closed form
(`scaled_gaussian_even_moment`).

No new axioms: the proof is the parent moment, the standard dilation rule for
the Lebesgue integral, and elementary `√`/power bookkeeping.
-/

open Real MeasureTheory
open scoped Nat

namespace AreaOfCircleOQ07OQ05OQ01OQ02

/-- **Integrability of `x^{2n} e^{-a x²}` for `a > 0`.**  The same Gaussian-decay
argument as the unscaled case, after absorbing `a` into the exponent. -/
theorem integrable_pow_mul_scaled_gaussian (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => x ^ (2 * n) * Real.exp (-a * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := a) ha (s := (2 * n : ℕ)) ?_
  · refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.rpow_natCast]
  · have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The scaled general even moment of the Gaussian (closed form).**
`∫_{-∞}^{∞} x^{2n} e^{-a x²} dx = (2n-1)‼ · √(π/a) / (2a)^n` for every `a > 0`,
obtained from the unscaled parent moment by the dilation `x ↦ √a · x`. -/
theorem scaled_gaussian_even_moment (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-a * x ^ 2)
      = ((2 * n - 1)‼ : ℝ) * Real.sqrt (Real.pi / a) / (2 * a) ^ n := by
  -- `s = √a`, the dilation factor.
  set s : ℝ := Real.sqrt a with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr ha
  have hssq : s ^ 2 = a := Real.sq_sqrt ha.le
  -- The unscaled integrand.
  set g : ℝ → ℝ := fun y => y ^ (2 * n) * Real.exp (-y ^ 2) with hg
  -- Dilation rule: `∫ g(s·x) = |s⁻¹| · ∫ g`.
  have hdil := Measure.integral_comp_mul_left g s
  -- Identify `g (s·x) = aⁿ · (x^{2n} e^{-a x²})` pointwise.
  have hpt : ∀ x : ℝ, g (s * x) = a ^ n * (x ^ (2 * n) * Real.exp (-a * x ^ 2)) := by
    intro x
    simp only [hg]
    have h1 : (s * x) ^ (2 * n) = a ^ n * x ^ (2 * n) := by
      rw [mul_pow, pow_mul, hssq]
    have h2 : -(s * x) ^ 2 = -a * x ^ 2 := by
      rw [mul_pow, hssq]; ring
    rw [h1, h2]; ring
  -- Rewrite the dilated integral as `aⁿ · I`, where `I` is the target integral.
  have hleft : (∫ x : ℝ, g (s * x))
      = a ^ n * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-a * x ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- The right side of the dilation rule, via the parent moment.
  have hpar := AreaOfCircleOQ07OQ05OQ01.gaussian_even_moment n
  have hright : (|s⁻¹| • ∫ y : ℝ, g y)
      = s⁻¹ * (((2 * n - 1)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n) := by
    rw [hg, hpar, smul_eq_mul, abs_of_pos (inv_pos.mpr hspos)]
  -- Assemble: `aⁿ · I = s⁻¹ · (parent value)`.
  rw [hleft, hright] at hdil
  -- Solve for `I` and match the closed form.
  have hanpos : (0 : ℝ) < a ^ n := pow_pos ha n
  have hI : ∫ x : ℝ, x ^ (2 * n) * Real.exp (-a * x ^ 2)
      = s⁻¹ * (((2 * n - 1)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n) / a ^ n := by
    field_simp at hdil ⊢
    linarith [hdil]
  rw [hI]
  -- Closed-form bookkeeping: `√(π/a) = √π / s` and `(2a)^n = 2^n aⁿ`.
  have hsqrt : Real.sqrt (Real.pi / a) = Real.sqrt Real.pi / s := by
    rw [hs, Real.sqrt_div Real.pi_pos.le]
  rw [hsqrt, mul_pow]
  field_simp

/-- Sanity check: `a = 1` recovers the parent's unscaled even moment. -/
theorem scaled_gaussian_even_moment_one (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(1 : ℝ) * x ^ 2)
      = ((2 * n - 1)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n := by
  have h := scaled_gaussian_even_moment n (a := 1) one_pos
  simpa using h

/-- Sanity check: the second moment (`n = 1`) of the scaled Gaussian is
`√(π/a) / (2a)` — twice the half-line value `√(π/a)/(4a)` of sibling
`area-of-circle-oq-07-oq-02-oq-02`, as the whole line doubles the `(0,∞)` half. -/
theorem scaled_gaussian_second_moment {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2)
      = Real.sqrt (Real.pi / a) / (2 * a) := by
  have h := scaled_gaussian_even_moment 1 ha
  norm_num [Nat.doubleFactorial] at h
  simpa using h

end AreaOfCircleOQ07OQ05OQ01OQ02
