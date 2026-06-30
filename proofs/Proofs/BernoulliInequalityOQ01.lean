import Mathlib

/-
# Bernoulli's inequality: the sharp strict form and its equality characterization

**Open question (bernoulli-inequality-oq-01).** Bernoulli's inequality states
`1 + n·a ≤ (1 + a)ⁿ` for `a ≥ -1` and `n : ℕ`.  The weak inequality is
`one_add_mul_le_pow` in Mathlib.  The *strict* version is sharper but more delicate:
the discarded quadratic term `C(n,2)·a²` is strictly positive exactly when `a ≠ 0`
and `n ≥ 2`.

This file proves the **complete, sharp picture** over the full domain `a > -1`:

* `one_add_mul_lt_pow` : the strict inequality `1 + n·a < (1 + a)ⁿ` for **every**
  `a > -1` with `a ≠ 0` and `n ≥ 2`.  In particular this covers the negative
  subrange `-1 < a < 0`, where the linear lower bound `1 + n·a` can be negative.
* `one_add_mul_lt_pow_iff` : the strict inequality holds **iff** `a ≠ 0 ∧ 2 ≤ n`.
* `one_add_mul_eq_pow_iff` : equality `1 + n·a = (1 + a)ⁿ` holds **iff** `a = 0 ∨ n ≤ 1`.

These three statements together pin down precisely when Bernoulli's inequality is
strict, an equality, or fails to be strict.

**Relation to Mathlib and the gallery.** Mathlib has only the weak integer-power form
`one_add_mul_le_pow` and an `rpow` strict form
(`one_add_mul_self_lt_rpow_one_add`); it has no strict *integer*-power Bernoulli.
The gallery's `binomial-theorem-oq-05` proves the strict form only for `a > 0`.
The contribution here is the extension to the full domain `a > -1` (the genuinely
harder negative range) together with the two-sided `iff` characterizations of
strictness and equality, none of which appear in Mathlib or the gallery.
-/

namespace BernoulliInequalityOQ01

variable {a : ℝ}

/-- **Strict Bernoulli inequality (sharp form).** For every real `a > -1` with `a ≠ 0`
and every `n ≥ 2`, the binomial power strictly exceeds its first-order lower bound:
`1 + n·a < (1 + a)ⁿ`.

Unlike the gallery's `binomial-theorem-oq-05` version (which assumes `a > 0`), this
covers the full domain `a > -1`, including `-1 < a < 0`. -/
theorem one_add_mul_lt_pow (ha : -1 < a) (ha0 : a ≠ 0) :
    ∀ {n : ℕ}, 2 ≤ n → 1 + n * a < (1 + a) ^ n := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      -- `n = 2`:  `(1 + a)² = 1 + 2a + a²`, and `a² > 0`.
      push_cast
      nlinarith [ha2]
  | succ m hm ih =>
      have hmpos : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
      -- Multiply the inductive estimate by the positive factor `1 + a`.
      have step : (1 + (m : ℝ) * a) * (1 + a) < (1 + a) ^ m * (1 + a) :=
        mul_lt_mul_of_pos_right ih h1a
      -- Expand the left side: it dominates `1 + (m+1)·a` since `m·a² > 0`.
      have hexp : 1 + ((m : ℝ) + 1) * a < (1 + (m : ℝ) * a) * (1 + a) := by
        nlinarith [ha2, hmpos]
      push_cast
      calc 1 + ((m : ℝ) + 1) * a
            < (1 + (m : ℝ) * a) * (1 + a) := hexp
        _ < (1 + a) ^ m * (1 + a) := step
        _ = (1 + a) ^ (m + 1) := by ring

/-- **Equality case is sharp.** For `a > -1`, Bernoulli's inequality is strict exactly
when `a ≠ 0` and `n ≥ 2`. -/
theorem one_add_mul_lt_pow_iff (ha : -1 < a) {n : ℕ} :
    1 + n * a < (1 + a) ^ n ↔ a ≠ 0 ∧ 2 ≤ n := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at h
    · by_contra hn
      push_neg at hn
      interval_cases n <;> simp_all
  · rintro ⟨ha0, hn⟩
    exact one_add_mul_lt_pow ha ha0 hn

/-- **Equality characterization.** For `a > -1`, equality `1 + n·a = (1 + a)ⁿ` holds
exactly when `a = 0` or `n ≤ 1`. -/
theorem one_add_mul_eq_pow_iff (ha : -1 < a) {n : ℕ} :
    1 + n * a = (1 + a) ^ n ↔ a = 0 ∨ n ≤ 1 := by
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hn⟩ := hcon
    have hlt := one_add_mul_lt_pow ha ha0 (by omega : 2 ≤ n)
    linarith
  · rintro (rfl | hn)
    · simp
    · interval_cases n <;> simp

/-- Concrete positive case: `1 + 5·1 = 6 < 32 = (1 + 1)⁵`. -/
example : (1 : ℝ) + 5 * 1 < (1 + 1) ^ 5 :=
  one_add_mul_lt_pow (by norm_num) (by norm_num) (by norm_num)

/-- Concrete **negative** case (outside the gallery's `a > 0` strict version):
`1 + 4·(−1/2) = −1 < 1/16 = (1 − 1/2)⁴`. -/
example : (1 : ℝ) + 4 * (-1 / 2) < (1 + (-1 / 2)) ^ 4 :=
  one_add_mul_lt_pow (by norm_num) (by norm_num) (by norm_num)

/-- Boundary of strictness: with `n = 1` Bernoulli's inequality is an equality. -/
example (a : ℝ) (ha : -1 < a) : 1 + (1 : ℕ) * a = (1 + a) ^ 1 :=
  (one_add_mul_eq_pow_iff ha).mpr (Or.inr le_rfl)

end BernoulliInequalityOQ01
