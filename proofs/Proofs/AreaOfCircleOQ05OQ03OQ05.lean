/-
  The Even Moments of the Gaussian are Double Factorials
  (area-of-circle-oq-05-oq-03-oq-05)

  The sibling `area-of-circle-oq-05-oq-03-oq-04` ("the moment & cumulant
  generating function of the Gaussian") proves that the moment generating
  function of the standard normal `N(0,1)` is the single entire function

      M(s) = ∫_ℝ e^{s x} (e^{-x²/2}/√(2π)) dx = e^{s²/2}.

  That generating function *encodes* every moment as a Taylor coefficient, but it
  never exhibits the moments themselves.  Here we evaluate them in closed form.
  The Gaussian's moments are the textbook capstone of the Gaussian-integral
  lineage `area-of-circle-oq-05`: every even moment is a double factorial and
  every odd moment vanishes:

      ∫_ℝ x^{2n} e^{-x²/2} dx = (2n-1)‼ · √(2π),                          (★)
      ∫_ℝ x^{2n+1} e^{-x²/2} dx = 0,                                       (★★)

  and after the probability normalization `/√(2π)`,

      E[X^{2n}] = (2n-1)‼,        E[X^{2n+1}] = 0          (X ~ N(0,1)).   (★★★)

  In particular the variance is `E[X²] = 1‼ = 1` and the kurtosis numerator is
  `E[X⁴] = 3‼ = 3` (so the excess kurtosis `E[X⁴] - 3 = 0`, the defining flatness
  of the normal).  Formula (★★★) is the univariate case of the Wick / Isserlis
  theorem: the `2n`-th Gaussian moment counts the `(2n-1)‼` perfect matchings of
  `2n` points.

  METHOD.
  • The companion identity for the *un-normalized* Gaussian weight `e^{-x²}`,

        ∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ,                        (A)

    is obtained by folding the integrand onto the half-line (`integral_comp_abs`,
    valid because `x^{2n} e^{-x²}` is even) and applying Mathlib's Gamma-function
    evaluation of the half-line moment integral
    `integral_rpow_mul_exp_neg_mul_rpow` (the substitution `u = x²`), together
    with the half-integer special value of the Gamma function
    `Real.Gamma_nat_add_half`:  `Γ(n + 1/2) = (2n-1)‼ √π / 2ⁿ`.
  • The Gaussian normalization `e^{-x²/2}` (★) follows from (A) by the linear
    rescaling `x ↦ x/√2` (`integral_comp_div`), which converts `e^{-x²}` into
    `e^{-x²/2}` and contributes exactly the factor `√2` that upgrades `√π` to
    `√(2π)`.
  • The odd moments (★★) vanish because the integrand is odd and Lebesgue measure
    is reflection-invariant (`integral_neg_eq_self`).

  Everything is proved with 0 sorries and 0 axioms.

  References:
  - Gaussian moments / Wick's theorem: Billingsley, Probability and Measure, §21;
    Isserlis (1918); Janson, Gaussian Hilbert Spaces, Thm 1.28.
  - Mathlib: MeasureTheory.Integral.Gamma (`integral_rpow_mul_exp_neg_mul_rpow`),
    Analysis.SpecialFunctions.Gaussian.GaussianIntegral (`Real.Gamma_nat_add_half`).
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real MeasureTheory Set
open scoped Real Nat

namespace GaussianMoments

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  THE UN-NORMALIZED EVEN MOMENT  ∫ x^{2n} e^{-x²} = (2n-1)‼ √π / 2ⁿ
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The even moments of the weight `e^{-x²}`.**

      ∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ.

    Proof: the integrand is even, so the full-line integral is twice the half-line
    integral (`integral_comp_abs`); the half-line integral is `½ Γ(n + ½)` by the
    Gamma evaluation `integral_rpow_mul_exp_neg_mul_rpow` (substitution `u = x²`);
    and `Γ(n + ½) = (2n-1)‼ √π / 2ⁿ` is `Real.Gamma_nat_add_half`. -/
theorem integral_pow_mul_exp_neg_sq (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = ((2 * n - 1)‼ : ℝ) * Real.sqrt π / 2 ^ n := by
  -- Fold the even integrand onto the half-line.
  have hdouble : ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)
      = 2 * ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) := by
    calc ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)
        = ∫ x : ℝ, (fun y : ℝ => y ^ (2 * n) * Real.exp (-y ^ 2)) |x| := by
          apply integral_congr_ae
          filter_upwards with x
          show x ^ (2 * n) * Real.exp (-x ^ 2) = |x| ^ (2 * n) * Real.exp (-|x| ^ 2)
          rw [show |x| ^ (2 * n) = x ^ (2 * n) from by rw [pow_mul, pow_mul, sq_abs], sq_abs]
      _ = 2 * ∫ x in Ioi (0 : ℝ), (fun y : ℝ => y ^ (2 * n) * Real.exp (-y ^ 2)) x :=
          integral_comp_abs (f := fun y : ℝ => y ^ (2 * n) * Real.exp (-y ^ 2))
      _ = 2 * ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) := rfl
  rw [hdouble]
  -- Evaluate the half-line moment integral via the Gamma function.
  have hI : ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2)
      = (1 / 2 : ℝ) * Real.Gamma ((n : ℝ) + 1 / 2) := by
    have hb := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((2 * n : ℕ) : ℝ)) (b := 1)
        (by norm_num) (by have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by positivity
                          linarith) (by norm_num)
    rw [Real.one_rpow, one_mul] at hb
    rw [show (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 by push_cast; ring] at hb
    rw [← hb]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    dsimp only
    rw [Real.rpow_natCast, neg_one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hI, Real.Gamma_nat_add_half]
  ring

/-- **The Gaussian integral as the `n = 0` case.**  `∫_ℝ e^{-x²} dx = √π`. -/
theorem integral_exp_neg_sq : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt π := by
  have h := integral_pow_mul_exp_neg_sq 0
  have hn : (2 * 0 - 1)‼ = 1 := by decide
  rw [hn] at h
  simpa using h

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  THE GAUSSIAN EVEN MOMENT  ∫ x^{2n} e^{-x²/2} = (2n-1)‼ √(2π)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The even moments of the standard Gaussian weight `e^{-x²/2}`.**

      ∫_ℝ x^{2n} e^{-x²/2} dx = (2n-1)‼ · √(2π).

    Obtained from the `e^{-x²}` moment by the rescaling `x ↦ x/√2`
    (`integral_comp_div`): the substitution turns `e^{-x²}` into `e^{-x²/2}`,
    pulls out `(√2)^{2n} = 2ⁿ` from `x^{2n}`, and contributes the Jacobian `√2`
    that promotes `√π` to `√(2π)`. -/
theorem integral_pow_mul_gaussian (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2 / 2)
      = ((2 * n - 1)‼ : ℝ) * Real.sqrt (2 * π) := by
  have hbase := integral_pow_mul_exp_neg_sq n
  have hcd := MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => y ^ (2 * n) * Real.exp (-y ^ 2)) (Real.sqrt 2)
  rw [hbase] at hcd
  -- Rewrite the substituted integrand `(x/√2)^{2n} e^{-(x/√2)²}` in clean form.
  have hLrw : (∫ x : ℝ, (x / Real.sqrt 2) ^ (2 * n) * Real.exp (-(x / Real.sqrt 2) ^ 2))
      = (1 / (2 : ℝ) ^ n) * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2 / 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    have e1 : (x / Real.sqrt 2) ^ (2 * n) = x ^ (2 * n) / 2 ^ n := by
      rw [div_pow, pow_mul (Real.sqrt 2) 2 n, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have e2 : -(x / Real.sqrt 2) ^ 2 = -x ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [e1, e2]; ring
  rw [hLrw] at hcd
  -- `hcd : (1/2ⁿ) · M = √2 · ((2n-1)‼ √π / 2ⁿ)`.  Cancel `1/2ⁿ`.
  have hfinal : (1 / (2 : ℝ) ^ n) * (∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2 / 2))
      = (1 / (2 : ℝ) ^ n) * (((2 * n - 1)‼ : ℝ) * Real.sqrt (2 * π)) := by
    rw [hcd, smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) π]
    ring
  exact mul_left_cancel₀ (by positivity : (1 / (2 : ℝ) ^ n) ≠ 0) hfinal

/-- **The normalized even moments of `N(0,1)`:**  `E[X^{2n}] = (2n-1)‼`.

      ∫_ℝ x^{2n} · (e^{-x²/2}/√(2π)) dx = (2n-1)‼. -/
theorem gaussian_even_moment (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π)) = ((2 * n - 1)‼ : ℝ) := by
  have hpos : Real.sqrt (2 * π) ≠ 0 := by positivity
  simp_rw [← mul_div_assoc]
  rw [integral_div, integral_pow_mul_gaussian, mul_div_assoc, div_self hpos, mul_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE ODD MOMENTS VANISH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **All odd moments of the Gaussian vanish.**

      ∫_ℝ x^{2n+1} e^{-x²/2} dx = 0.

    The integrand is odd and Lebesgue measure is reflection-invariant, so the
    integral equals its own negation (`integral_neg_eq_self`). -/
theorem integral_odd_pow_mul_gaussian (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * Real.exp (-x ^ 2 / 2) = 0 := by
  have step : (∫ x : ℝ, x ^ (2 * n + 1) * Real.exp (-x ^ 2 / 2))
      = -∫ x : ℝ, x ^ (2 * n + 1) * Real.exp (-x ^ 2 / 2) := by
    conv_lhs =>
      rw [← integral_neg_eq_self (fun x : ℝ => x ^ (2 * n + 1) * Real.exp (-x ^ 2 / 2)) volume]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    show (-x) ^ (2 * n + 1) * Real.exp (-(-x) ^ 2 / 2)
      = -(x ^ (2 * n + 1) * Real.exp (-x ^ 2 / 2))
    rw [Odd.neg_pow ⟨n, by ring⟩, neg_sq]
    ring
  linarith [step]

/-- **The normalized odd moments of `N(0,1)`:**  `E[X^{2n+1}] = 0`. -/
theorem gaussian_odd_moment (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π)) = 0 := by
  have hpos : Real.sqrt (2 * π) ≠ 0 := by positivity
  simp_rw [← mul_div_assoc]
  rw [integral_div, integral_odd_pow_mul_gaussian, zero_div]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  LOW-ORDER MOMENTS (VARIANCE AND KURTOSIS)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The variance of `N(0,1)` is `1`:**  `E[X²] = 1‼ = 1`. -/
theorem gaussian_variance :
    ∫ x : ℝ, x ^ 2 * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π)) = 1 := by
  have h := gaussian_even_moment 1
  have hn : (2 * 1 - 1)‼ = 1 := by decide
  rw [hn] at h
  simpa using h

/-- **The fourth moment of `N(0,1)` is `3`:**  `E[X⁴] = 3‼ = 3`.
    Hence the excess kurtosis `E[X⁴] - 3 = 0`, the defining flatness of the
    normal distribution. -/
theorem gaussian_fourth_moment :
    ∫ x : ℝ, x ^ 4 * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π)) = 3 := by
  have h := gaussian_even_moment 2
  have hn : (2 * 2 - 1)‼ = 3 := by decide
  rw [hn] at h
  simpa using h

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The Even Moments of the Gaussian are Double Factorials  (oq-05-oq-03-oq-05)

### What's proved (0 sorries, 0 axioms):
- `integral_pow_mul_exp_neg_sq`: ∫ x^{2n} e^{-x²} = (2n-1)‼ √π / 2ⁿ.
- `integral_exp_neg_sq`: ∫ e^{-x²} = √π (the Gaussian integral, n = 0).
- `integral_pow_mul_gaussian`: **∫ x^{2n} e^{-x²/2} = (2n-1)‼ √(2π)**.
- `gaussian_even_moment`: **E[X^{2n}] = (2n-1)‼** for X ~ N(0,1).
- `integral_odd_pow_mul_gaussian` / `gaussian_odd_moment`: all odd moments vanish.
- `gaussian_variance`: E[X²] = 1;  `gaussian_fourth_moment`: E[X⁴] = 3.

### Significance:
The closed form `E[X^{2n}] = (2n-1)‼` is the univariate Wick/Isserlis theorem:
the `2n`-th Gaussian moment counts the `(2n-1)‼` perfect matchings of `2n` points.
It makes concrete what the sibling MGF entry (oq-04) only encodes as the Taylor
coefficients of `e^{s²/2}`, and it derives the normalization `√(2π)` of the
Gaussian-integral lineage (oq-05) as a moment.
-/

end GaussianMoments
