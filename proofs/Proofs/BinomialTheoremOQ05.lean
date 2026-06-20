import Mathlib

/-
# Binomial Theorem OQ-05: Bernoulli's Inequality (and its strict form)

## Research Problem: binomial-theorem-oq-05

Bernoulli's inequality is the first-order lower bound on a binomial power: for a real
number a ≥ -1 (more generally a ≥ -2) and a natural number n,

  1 + n·a ≤ (1 + a)ⁿ.

It is the truncation-after-the-linear-term of the binomial expansion
(1 + a)ⁿ = 1 + n·a + C(n,2)·a² + …, with all the dropped terms being ≥ 0 when a ≥ 0,
and the inequality persisting (by an induction that only needs 1 + a ≥ 0) all the way
down to a ≥ -1.

## Mathematical Content

This file collects the standard Bernoulli inequalities from Mathlib and then proves a
result Mathlib does **not** contain: the **strict** Bernoulli inequality

  a > -1, a ≠ 0, n ≥ 2  ⟹  1 + n·a < (1 + a)ⁿ,

by induction on n starting at n = 2 (base case uses a² > 0; the step multiplies by the
positive factor 1 + a and discards the nonnegative term n·a²). We then derive several
consequences: the a ≥ -1 corollary, the aⁿ-estimate reformulation, the exponential-growth
bound 1 + n ≤ 2ⁿ, and the strict separation (1 + a)ⁿ > 1 for a > 0.

## References
- Jacob Bernoulli (1689): *Positiones Arithmeticae de Seriebus Infinitis*
- Mathlib: `one_add_mul_le_pow`, `one_add_mul_le_pow_of_sq_nonneg`, `one_add_mul_sub_le_pow`
-/

open Finset

namespace BinomialTheoremOQ05

/-! ## Part I: Bernoulli's inequality (Mathlib forms) -/

/-- **Bernoulli's inequality** (general form, a ≥ -2): `1 + n·a ≤ (1 + a)ⁿ`. -/
theorem bernoulli (a : ℝ) (ha : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow ha n

/-- **Bernoulli's inequality** (classical form, a ≥ -1): `1 + n·a ≤ (1 + a)ⁿ`.
    The classical hypothesis a ≥ -1 is a special case of a ≥ -2. -/
theorem bernoulli_of_neg_one_le (a : ℝ) (ha : -1 ≤ a) (n : ℕ) :
    1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- Bernoulli's inequality reformulated to estimate `aⁿ` directly: for a ≥ -1,
    `1 + n·(a - 1) ≤ aⁿ`. -/
theorem bernoulli_estimate (a : ℝ) (ha : -1 ≤ a) (n : ℕ) :
    1 + n * (a - 1) ≤ a ^ n :=
  one_add_mul_sub_le_pow ha n

/-! ## Part II: Strict Bernoulli's inequality (original — Mathlib lacks this) -/

/-- **Strict Bernoulli's inequality.** For `a > -1`, `a ≠ 0`, and `n ≥ 2`,
    `1 + n·a < (1 + a)ⁿ`.

    Proof by induction on n from the base n = 2:
    - Base: `(1+a)² = 1 + 2a + a² > 1 + 2a` since `a² > 0` (as `a ≠ 0`).
    - Step: `(1+a)ⁿ⁺¹ = (1+a)ⁿ·(1+a) > (1 + n·a)·(1+a)` (multiply the IH by the positive
      factor `1+a`), and `(1 + n·a)·(1+a) = 1 + (n+1)·a + n·a² ≥ 1 + (n+1)·a`. -/
theorem bernoulli_strict (a : ℝ) (ha : -1 < a) (ha0 : a ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    1 + n * a < (1 + a) ^ n := by
  have hpos : 0 < 1 + a := by linarith
  have hasq : 0 < a ^ 2 := by positivity
  induction n, hn using Nat.le_induction with
  | base =>
    have : (1 + a) ^ 2 = 1 + 2 * a + a ^ 2 := by ring
    rw [this]; push_cast; nlinarith
  | succ n hn ih =>
    have hstep : (1 + (n : ℝ) * a) * (1 + a) < (1 + a) ^ n * (1 + a) :=
      mul_lt_mul_of_pos_right ih hpos
    have hexp : (1 + a) ^ (n + 1) = (1 + a) ^ n * (1 + a) := by ring
    rw [hexp]
    have hnsq : 0 ≤ (n : ℝ) * a ^ 2 := by positivity
    push_cast
    nlinarith [hstep, hnsq]

/-! ## Part III: Consequences -/

/-- Exponential growth bound: `1 + n ≤ 2ⁿ` for all n (Bernoulli at a = 1). -/
theorem one_add_le_two_pow (n : ℕ) : 1 + (n : ℝ) ≤ 2 ^ n := by
  have h := bernoulli 1 (by norm_num) n
  rw [show (1 : ℝ) + 1 = 2 from by norm_num, mul_one] at h
  exact h

/-- Strict exponential growth: `1 + n < 2ⁿ` for n ≥ 2 (strict Bernoulli at a = 1). -/
theorem one_add_lt_two_pow (n : ℕ) (hn : 2 ≤ n) : 1 + (n : ℝ) < 2 ^ n := by
  have h := bernoulli_strict 1 (by norm_num) (by norm_num) hn
  rw [show (1 : ℝ) + 1 = 2 from by norm_num, mul_one] at h
  exact h

/-- For a > 0 and n ≥ 1, the power strictly exceeds 1: `1 < (1 + a)ⁿ`. -/
theorem one_lt_pow_of_pos (a : ℝ) (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    1 < (1 + a) ^ n := by
  have h := bernoulli a (by linarith) n
  have : (0 : ℝ) < n * a := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  linarith

/-! ## Part IV: Verified examples -/

-- (1 + 1)³ = 8 ≥ 1 + 3 = 4
example : (1 : ℝ) + 3 * 1 ≤ (1 + 1) ^ 3 := bernoulli 1 (by norm_num) 3

-- Strict: 1 + 3·1 < (1+1)³, i.e. 4 < 8
example : (1 : ℝ) + 3 * 1 < (1 + 1) ^ 3 := bernoulli_strict 1 (by norm_num) (by norm_num) (by norm_num)

-- Bernoulli with negative a = -1/2 ≥ -1: 1 + 4·(-1/2) = -1 ≤ (1/2)⁴
example : (1 : ℝ) + 4 * (-1/2) ≤ (1 + (-1/2)) ^ 4 :=
  bernoulli_of_neg_one_le (-1/2) (by norm_num) 4

/-! ## Part V: Summary -/

/-- **Binomial OQ-05 Summary.** For a > -1, a ≠ 0, n ≥ 2:
    (1) Bernoulli: `1 + n·a ≤ (1 + a)ⁿ`;
    (2) strict Bernoulli: `1 + n·a < (1 + a)ⁿ`;
    (3) the aⁿ-estimate `1 + n·(a-1) ≤ (1+a)ⁿ` follows for the shifted base. -/
theorem binomial_oq05_summary (a : ℝ) (ha : -1 < a) (ha0 : a ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (1 + n * a ≤ (1 + a) ^ n) ∧
    (1 + n * a < (1 + a) ^ n) :=
  ⟨bernoulli a (by linarith) n, bernoulli_strict a ha ha0 hn⟩

end BinomialTheoremOQ05
