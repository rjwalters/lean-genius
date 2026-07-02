import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

/-
# Basel Problem (OQ-03 → OQ-02): How far does the even-zeta product-reduction extend?

Open Question (child of OQ-03, "Multiple Zeta Values: relationship to single
zeta values"):

The parent entry (`BaselProblemOQ03`) evaluated ζ(2), ζ(4), ζ(6), ζ(8) via
Euler's formula and proved that every product of these even zeta values collapses
to a single even zeta value times a *tidy* rational — ζ(2)² = (5/2)·ζ(4),
ζ(2)·ζ(4) = (7/4)·ζ(6), ζ(4)² = (7/6)·ζ(8), … .  It stopped at weight 8.

**The question this file answers.** Does the "product of even zetas reduces to a
single even zeta" phenomenon continue past weight 8, and does the reduction
coefficient stay "nice"?  We push two weights further, to ζ(10) and ζ(12), and
find:

* The reduction *always* holds — this is forced by Euler's formula
  ζ(2k) = q_k · π^{2k} (`hasSum_zeta_nat`): matching π-powers turns any product of
  even zetas into a rational multiple of the single zeta of the summed weight.
* At weight 10 the coefficients are still tidy (33/20, 11/10, 11/4, 77/40, 385/32).
* **At weight 12 the coefficients stop being tidy** — 715/691, 2275/1382,
  3003/2764 — because the *irregular prime 691* enters through B₁₂ = -691/2730,
  putting a factor of 691 in the *numerator* of ζ(12) = 691·π¹²/638512875
  (638512875 = 3⁶·5³·7²·11·13 is coprime to 691).  Consequently every reduction
  coefficient P/ζ(12) acquires 691 in its *denominator*: 715/691, 2275/1382 =
  (5²·7·13)/(2·691), 3003/2764 = (3·7·11·13)/(4·691).  The prime 691 — the first
  irregular prime, the numerator of B₁₂, the modulus of Ramanujan's τ congruence
  — is exactly the arithmetic fingerprint that breaks the tidiness that held
  through weight 10.

## What is proved

Bernoulli numbers Mathlib does not stock, computed from the defining recursion:

* `bernoulli_ten`     : B₁₀ = 5/66
* `bernoulli_twelve`  : B₁₂ = -691/2730   (the "691" number)

Closed forms for the single zeta values, from `hasSum_zeta_nat`:

* `hasSum_zeta_ten`   : ζ(10) = π¹⁰/93555
* `hasSum_zeta_twelve`: ζ(12) = 691·π¹²/638512875

Weight-10 product reductions (tidy coefficients):

* `zeta_two_mul_eight`   : ζ(2)·ζ(8)   = (33/20)·ζ(10)
* `zeta_four_mul_six`    : ζ(4)·ζ(6)   = (11/10)·ζ(10)
* `zeta_two_sq_mul_six`  : ζ(2)²·ζ(6)  = (11/4)·ζ(10)
* `zeta_two_mul_four_sq` : ζ(2)·ζ(4)²  = (77/40)·ζ(10)
* `zeta_two_pow_five`    : ζ(2)⁵       = (385/32)·ζ(10)

Weight-12 product reductions (coefficients spoiled by 691):

* `zeta_six_sq`        : ζ(6)²       = (715/691)·ζ(12)
* `zeta_two_mul_ten`   : ζ(2)·ζ(10)  = (2275/1382)·ζ(12)
* `zeta_four_mul_eight`: ζ(4)·ζ(8)   = (3003/2764)·ζ(12)

## Status

Verified. Axioms: 0 (no `native_decide`). Sorries: 0.
-/

namespace BaselProblemOQ03OQ02

open scoped Real
open Nat Finset

/-! ## Bernoulli numbers B₁₀ and B₁₂

Mathlib stocks `bernoulli'_two`, `bernoulli'_three`, `bernoulli'_four` and stops
there.  The parent entry computed B₆ = 1/42 and B₈ = -1/30 from `bernoulli'_def`.
We continue the recursion two more even steps, to B₁₀ and B₁₂, using that the odd
Bernoulli numbers vanish. -/

theorem bernoulli'_five : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_seven : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_nine : bernoulli' 9 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_eleven : bernoulli' 11 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, Nat.choose]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five,
    bernoulli'_six, bernoulli'_seven, Nat.choose]

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five,
    bernoulli'_six, bernoulli'_seven, bernoulli'_eight, bernoulli'_nine, Nat.choose]

theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five,
    bernoulli'_six, bernoulli'_seven, bernoulli'_eight, bernoulli'_nine,
    bernoulli'_ten, bernoulli'_eleven, Nat.choose]

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]

theorem bernoulli_eight : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]

theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_ten]

/-- B₁₂ = -691/2730: the first Bernoulli number whose numerator is an irregular
prime.  This 691 is the arithmetic obstruction that spoils the tidiness of the
weight-12 product reductions below. -/
theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_twelve]

/-! ## Closed forms for ζ(10) and ζ(12)

`hasSum_zeta_two`, `hasSum_zeta_four` are in Mathlib; the parent added ζ(6), ζ(8);
we add ζ(10) and ζ(12). -/

theorem hasSum_zeta_six :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (π ^ 6 / 945) := by
  have h := hasSum_zeta_nat (k := 3) (by norm_num)
  simp only [(by norm_num : (2 * 3 : ℕ) = 6), (by norm_num : (2 * 3 - 1 : ℕ) = 5)] at h
  rw [bernoulli_six] at h
  convert h using 1
  rw [show (6 : ℕ)! = 720 from by norm_num]
  push_cast
  ring

theorem hasSum_zeta_eight :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8) (π ^ 8 / 9450) := by
  have h := hasSum_zeta_nat (k := 4) (by norm_num)
  simp only [(by norm_num : (2 * 4 : ℕ) = 8), (by norm_num : (2 * 4 - 1 : ℕ) = 7)] at h
  rw [bernoulli_eight] at h
  convert h using 1
  rw [show (8 : ℕ)! = 40320 from by norm_num]
  push_cast
  ring

theorem hasSum_zeta_ten :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 10) (π ^ 10 / 93555) := by
  have h := hasSum_zeta_nat (k := 5) (by norm_num)
  simp only [(by norm_num : (2 * 5 : ℕ) = 10), (by norm_num : (2 * 5 - 1 : ℕ) = 9)] at h
  rw [bernoulli_ten] at h
  convert h using 1
  rw [show (10 : ℕ)! = 3628800 from by norm_num]
  push_cast
  ring

theorem hasSum_zeta_twelve :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 12) (691 * π ^ 12 / 638512875) := by
  have h := hasSum_zeta_nat (k := 6) (by norm_num)
  simp only [(by norm_num : (2 * 6 : ℕ) = 12), (by norm_num : (2 * 6 - 1 : ℕ) = 11)] at h
  rw [bernoulli_twelve] at h
  convert h using 1
  rw [show (12 : ℕ)! = 479001600 from by norm_num]
  push_cast
  ring

/-! ## The single even zeta values as `tsum`s -/

theorem tsum_zeta_two : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

theorem tsum_zeta_four : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 = π ^ 4 / 90 :=
  hasSum_zeta_four.tsum_eq

theorem tsum_zeta_six : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 = π ^ 6 / 945 :=
  hasSum_zeta_six.tsum_eq

theorem tsum_zeta_eight : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8 = π ^ 8 / 9450 :=
  hasSum_zeta_eight.tsum_eq

theorem tsum_zeta_ten : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 = π ^ 10 / 93555 :=
  hasSum_zeta_ten.tsum_eq

theorem tsum_zeta_twelve : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 12 = 691 * π ^ 12 / 638512875 :=
  hasSum_zeta_twelve.tsum_eq

/-! ## Weight-10 product reductions — coefficients still tidy

Every product of even zeta values whose weights sum to 10 is a rational multiple
of ζ(10).  At this weight the coefficients remain small fractions, matching the
pattern of the parent entry's weight ≤ 8 relations. -/

/-- ζ(2)·ζ(8) = (33/20)·ζ(10). -/
theorem zeta_two_mul_eight :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8)
      = (33 / 20) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 := by
  rw [tsum_zeta_two, tsum_zeta_eight, tsum_zeta_ten]; ring

/-- ζ(4)·ζ(6) = (11/10)·ζ(10). -/
theorem zeta_four_mul_six :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6)
      = (11 / 10) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 := by
  rw [tsum_zeta_four, tsum_zeta_six, tsum_zeta_ten]; ring

/-- ζ(2)²·ζ(6) = (11/4)·ζ(10). -/
theorem zeta_two_sq_mul_six :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2 * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6)
      = (11 / 4) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 := by
  rw [tsum_zeta_two, tsum_zeta_six, tsum_zeta_ten]; ring

/-- ζ(2)·ζ(4)² = (77/40)·ζ(10). -/
theorem zeta_two_mul_four_sq :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) ^ 2
      = (77 / 40) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 := by
  rw [tsum_zeta_two, tsum_zeta_four, tsum_zeta_ten]; ring

/-- ζ(2)⁵ = (385/32)·ζ(10). -/
theorem zeta_two_pow_five :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 5
      = (385 / 32) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10 := by
  rw [tsum_zeta_two, tsum_zeta_ten]; ring

/-! ## Weight-12 product reductions — the tidiness breaks at 691

The reduction phenomenon persists: each product below is still a rational
multiple of ζ(12).  But because ζ(12) = 691·π¹²/638512875 carries the irregular
prime 691 (from B₁₂ = -691/2730) in its *numerator*, every reduction coefficient
P/ζ(12) picks up 691 in its *denominator*.  The tidy small fractions of weights
≤ 10 give way to 715/691, 2275/1382, 3003/2764 — the first visible degradation of
the "product of even zetas is a *simple* multiple of a single zeta" heuristic, a
direct fingerprint of the arithmetic of Bernoulli numbers. -/

/-- ζ(6)² = (715/691)·ζ(12).  The numerator 715 = 5·11·13 is tidy; the 691 in the
denominator is the shadow of the irregular prime sitting in ζ(12)'s numerator. -/
theorem zeta_six_sq :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6) ^ 2
      = (715 / 691) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 12 := by
  rw [tsum_zeta_six, tsum_zeta_twelve]; ring

/-- ζ(2)·ζ(10) = (2275/1382)·ζ(12), with 1382 = 2·691. -/
theorem zeta_two_mul_ten :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 10)
      = (2275 / 1382) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 12 := by
  rw [tsum_zeta_two, tsum_zeta_ten, tsum_zeta_twelve]; ring

/-- ζ(4)·ζ(8) = (3003/2764)·ζ(12), with 2764 = 4·691. -/
theorem zeta_four_mul_eight :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8)
      = (3003 / 2764) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 12 := by
  rw [tsum_zeta_four, tsum_zeta_eight, tsum_zeta_twelve]; ring

end BaselProblemOQ03OQ02
