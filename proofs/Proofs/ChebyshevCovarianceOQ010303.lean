import Mathlib
import Proofs.ChebyshevSumIntegralOQ0103

/-
# Covariance / correlation corollary of the continuous Chebyshev inequality

The parent entry
`chebyshev-sum-inequality-oq-01-oq-03` (`ChebyshevIntegralMonotone`) proves the
**continuous Chebyshev sum inequality** for monotone functions on an interval:

  (∫ₐᵇ f)(∫ₐᵇ g) ≤ (b − a) · ∫ₐᵇ f·g,                    (f, g both monotone)

with the inequality reversing when one function increases and the other decreases.

## What this proves

This entry recasts that analytic inequality in the language of **probability**: it is the
statement that monotone functions of a random variable are *positively correlated*.

Let `X` be uniformly distributed on `[a, b]` (with `a < b`), so that the expectation of a
function `h` is the average value `E[h] = (1/(b−a)) ∫ₐᵇ h`.  With this normalisation the
uniform law is a genuine probability distribution, `E[1] = 1` (`expectUnif_one`).  Define
the covariance in the usual way,

  Cov(f(X), g(X)) = E[f g] − E[f] E[g]   (`covUnif`).

Then:

* `covUnif_nonneg_of_monotoneOn` — if `f` and `g` are both monotone, `Cov(f(X),g(X)) ≥ 0`;
* `covUnif_nonpos_of_antitoneOn` — if `f` increases and `g` decreases, `Cov(f(X),g(X)) ≤ 0`;
* `expectUnif_mul_ge_of_monotoneOn` — the equivalent correlation form `E[f g] ≥ E[f] E[g]`;
* `expectUnif_mul_le_of_antitoneOn` — the reverse correlation `E[f g] ≤ E[f] E[g]`.

## Relation to the FKG / Harris inequality

The inequality `E[f g] ≥ E[f] E[g]` for comonotone `f, g` is exactly the **Harris–FKG
correlation inequality specialised to a chain**.  The general FKG inequality states that
on a finite distributive lattice equipped with a *log-supermodular* (positively associated)
measure, any two functions that are both increasing are positively correlated.  On a
*totally ordered* index set — here the interval `[a, b]`, a chain — log-supermodularity is
automatic for every measure, so the FKG hypothesis is vacuous and the conclusion reduces to
precisely the covariance statement proved here for the uniform (Lebesgue) law.  This entry
does **not** prove the general lattice FKG inequality; it establishes the one–dimensional
(chain) case, which is the classical correlation inequality of Chebyshev and Harris.

## Method

Purely a division by `(b − a)² > 0` from the parent's integral inequality.  Writing
`Iₕ := ∫ₐᵇ h`, the covariance is `Cov = I_{fg}/(b−a) − (I_f I_g)/(b−a)²`, and the parent
gives `I_f I_g ≤ (b−a) I_{fg}`, i.e. `(I_f I_g)/(b−a)² ≤ I_{fg}/(b−a)`.  No new analysis is
required beyond the parent theorem, so the result is fully verified with no extra axioms.

## Mathlib ingredients
- `ChebyshevIntegralMonotone.chebyshev_integral_monotoneOn` / `_antitoneOn` (the parent)
- `intervalIntegral.integral_const` (for `E[1] = 1`)
- ordered-field arithmetic (`div_le_div_iff`, `div_mul_div_comm`)
-/

open MeasureTheory Set

namespace ChebyshevCovariance

open ChebyshevIntegralMonotone

variable {a b : ℝ} {f g : ℝ → ℝ}

/-- Expectation of `h(X)` for a random variable `X` uniform on `[a, b]`:
`E[h] = (1/(b−a)) ∫ₐᵇ h`. -/
noncomputable def expectUnif (a b : ℝ) (h : ℝ → ℝ) : ℝ :=
  (∫ x in a..b, h x) / (b - a)

/-- Covariance of `f(X)` and `g(X)` for `X` uniform on `[a, b]`:
`Cov = E[f g] − E[f] E[g]`. -/
noncomputable def covUnif (a b : ℝ) (f g : ℝ → ℝ) : ℝ :=
  expectUnif a b (fun x => f x * g x) - expectUnif a b f * expectUnif a b g

/-- The uniform law on `[a, b]` (with `a < b`) is a probability distribution: `E[1] = 1`. -/
theorem expectUnif_one (hab : a < b) : expectUnif a b (fun _ => 1) = 1 := by
  have hL : (b - a) ≠ 0 := by linarith
  simp only [expectUnif, intervalIntegral.integral_const, smul_eq_mul, mul_one,
    div_self hL]

/-- **Positive correlation of monotone functions (covariance form).**
If `f` and `g` are both monotone on `[a, b]` (and `a < b`), then the covariance of `f(X)`
and `g(X)` for `X` uniform on `[a, b]` is nonnegative: `Cov(f(X), g(X)) ≥ 0`. -/
theorem covUnif_nonneg_of_monotoneOn
    (hab : a < b) (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    0 ≤ covUnif a b f g := by
  have hL : (0 : ℝ) < b - a := by linarith
  have hcheb := chebyshev_integral_monotoneOn hab.le hf hg
  simp only [covUnif, expectUnif]
  rw [div_mul_div_comm, sub_nonneg, div_le_div_iff₀ (mul_pos hL hL) hL]
  nlinarith [mul_le_mul_of_nonneg_right hcheb hL.le]

/-- **Negative correlation (covariance form).**
If `f` is monotone and `g` is antitone on `[a, b]` (and `a < b`), then the covariance of
`f(X)` and `g(X)` for `X` uniform on `[a, b]` is nonpositive: `Cov(f(X), g(X)) ≤ 0`. -/
theorem covUnif_nonpos_of_antitoneOn
    (hab : a < b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc a b)) :
    covUnif a b f g ≤ 0 := by
  have hL : (0 : ℝ) < b - a := by linarith
  have hcheb := chebyshev_integral_antitoneOn hab.le hf hg
  simp only [covUnif, expectUnif]
  rw [div_mul_div_comm, sub_nonpos, div_le_div_iff₀ hL (mul_pos hL hL)]
  nlinarith [mul_le_mul_of_nonneg_right hcheb hL.le]

/-- **Harris–FKG correlation inequality on the chain `[a, b]` (uniform law).**
For `X` uniform on `[a, b]` (with `a < b`) and `f, g` both monotone, `E[f g] ≥ E[f] E[g]`. -/
theorem expectUnif_mul_ge_of_monotoneOn
    (hab : a < b) (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    expectUnif a b f * expectUnif a b g ≤ expectUnif a b (fun x => f x * g x) := by
  have h := covUnif_nonneg_of_monotoneOn hab hf hg
  simp only [covUnif] at h
  linarith

/-- **Reverse correlation inequality (uniform law).**
For `X` uniform on `[a, b]` (with `a < b`), `f` monotone and `g` antitone, `E[f g] ≤ E[f] E[g]`. -/
theorem expectUnif_mul_le_of_antitoneOn
    (hab : a < b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc a b)) :
    expectUnif a b (fun x => f x * g x) ≤ expectUnif a b f * expectUnif a b g := by
  have h := covUnif_nonpos_of_antitoneOn hab hf hg
  simp only [covUnif] at h
  linarith

end ChebyshevCovariance
