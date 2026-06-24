import Mathlib

/-
# Strict Bernoulli over Mathlib's full weak domain `-2 ≤ a`

**Open question (bernoulli-inequality-oq-01-oq-01).** Mathlib's weak Bernoulli
inequality `one_add_mul_le_pow` holds on the full domain `-2 ≤ a` (not merely
`a ≥ -1`).  The parent entry `bernoulli-inequality-oq-01`
(`BernoulliInequalityOQ01.lean`) sharpens it to the *strict* form
`1 + n·a < (1 + a)ⁿ` — but only over `a > -1`, where the elementary induction
multiplies the inductive estimate by the *positive* factor `1 + a`.

For `-2 ≤ a ≤ -1` that factor is `≤ 0`, so the induction collapses.  This file
proves the strict inequality on the **entire weak domain** `-2 ≤ a`, matching the
reach of `one_add_mul_le_pow`:

* `one_add_mul_lt_pow_full` : for every `-2 ≤ a` with `a ≠ 0` and every `n ≥ 2`,
  `1 + n·a < (1 + a)ⁿ`.  The hard new range is `-2 ≤ a ≤ -1`.
* `one_add_mul_lt_pow_full_iff` : strictness holds **iff** `a ≠ 0 ∧ 2 ≤ n`.
* `one_add_mul_eq_pow_full_iff` : equality holds **iff** `a = 0 ∨ n ≤ 1`.

**The negative-tail argument.** For `-2 ≤ a ≤ -1` we have `|1 + a| ≤ 1`, hence
`(1 + a)ⁿ ≥ -1`.  Meanwhile `a ≤ -1` forces `1 + n·a ≤ 1 - n`, which is `< -1`
as soon as `n ≥ 3`; so the power already overshoots the line.  The single
remaining value `n = 2` is the unconditional identity `(1+a)² - (1+2a) = a² > 0`.
This is a genuinely different mechanism from the `a > -1` induction and is what
extends the strict inequality past the sign change of `1 + a`.

**Relation to Mathlib and the gallery.** Mathlib has the weak integer form
`one_add_mul_le_pow` (domain `-2 ≤ a`) and an `rpow` strict form
(`one_add_mul_self_lt_rpow_one_add`), but no strict *integer*-power Bernoulli on
the negative range. The parent entry covers only `a > -1`; the contribution here
is the extension to `-2 ≤ a` together with the two-sided characterizations on
that full domain.
-/

namespace BernoulliInequalityOQ01OQ01

variable {a : ℝ}

/-- Strict Bernoulli on the *positive-factor* range `a > -1`, by the standard
induction (the inductive estimate is multiplied by `1 + a > 0`).  This is the
range already handled by the parent entry; we re-prove it here to keep the file
self-contained. -/
theorem one_add_mul_lt_pow_pos (ha : -1 < a) (ha0 : a ≠ 0) :
    ∀ {n : ℕ}, 2 ≤ n → 1 + n * a < (1 + a) ^ n := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      push_cast
      nlinarith [ha2]
  | succ m hm ih =>
      have hmpos : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
      have step : (1 + (m : ℝ) * a) * (1 + a) < (1 + a) ^ m * (1 + a) :=
        mul_lt_mul_of_pos_right ih h1a
      have hexp : 1 + ((m : ℝ) + 1) * a < (1 + (m : ℝ) * a) * (1 + a) := by
        nlinarith [ha2, hmpos]
      push_cast
      calc 1 + ((m : ℝ) + 1) * a
            < (1 + (m : ℝ) * a) * (1 + a) := hexp
        _ < (1 + a) ^ m * (1 + a) := step
        _ = (1 + a) ^ (m + 1) := by ring

/-- **Strict Bernoulli inequality on Mathlib's full weak domain.** For every real
`-2 ≤ a` with `a ≠ 0` and every `n ≥ 2`, the binomial power strictly exceeds its
first-order lower bound: `1 + n·a < (1 + a)ⁿ`.

This extends the parent entry (which assumes `a > -1`) across the sign change of
`1 + a` to the entire range on which `one_add_mul_le_pow` holds. -/
theorem one_add_mul_lt_pow_full (ha : -2 ≤ a) (ha0 : a ≠ 0) :
    ∀ {n : ℕ}, 2 ≤ n → 1 + n * a < (1 + a) ^ n := by
  intro n hn
  rcases le_or_gt a (-1) with hle | hgt
  · -- `-2 ≤ a ≤ -1`: the factor `1 + a` is `≤ 0`, so the induction fails.
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    obtain rfl | hn3 : n = 2 ∨ 3 ≤ n := by omega
    · -- `n = 2`: unconditional identity `(1+a)² - (1+2a) = a² > 0`.
      push_cast
      nlinarith [ha2]
    · -- `n ≥ 3`: `(1+a)ⁿ ≥ -1` while `1 + n·a ≤ 1 - n < -1`.
      have hb : |1 + a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hpw : |(1 + a) ^ n| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hb
      have hpow : (-1 : ℝ) ≤ (1 + a) ^ n := (abs_le.mp hpw).1
      have hn3' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hna : (n : ℝ) * a ≤ -(n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      linarith
  · -- `a > -1`: positive factor, use the induction.
    exact one_add_mul_lt_pow_pos hgt ha0 hn

/-- **Sharp strictness on the full domain.** For `-2 ≤ a`, Bernoulli's inequality
is strict exactly when `a ≠ 0` and `n ≥ 2`. -/
theorem one_add_mul_lt_pow_full_iff (ha : -2 ≤ a) {n : ℕ} :
    1 + n * a < (1 + a) ^ n ↔ a ≠ 0 ∧ 2 ≤ n := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at h
    · by_contra hn
      push_neg at hn
      interval_cases n <;> simp_all
  · rintro ⟨ha0, hn⟩
    exact one_add_mul_lt_pow_full ha ha0 hn

/-- **Equality characterization on the full domain.** For `-2 ≤ a`, equality
`1 + n·a = (1 + a)ⁿ` holds exactly when `a = 0` or `n ≤ 1`. -/
theorem one_add_mul_eq_pow_full_iff (ha : -2 ≤ a) {n : ℕ} :
    1 + n * a = (1 + a) ^ n ↔ a = 0 ∨ n ≤ 1 := by
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hn⟩ := hcon
    have hlt := one_add_mul_lt_pow_full ha ha0 (by omega : 2 ≤ n)
    linarith
  · rintro (rfl | hn)
    · simp
    · interval_cases n <;> simp

/-- Concrete case in the new negative range `-2 ≤ a < -1`, outside the parent's
`a > -1` domain: `1 + 3·(−3/2) = −7/2 < −1/8 = (1 − 3/2)³`. -/
example : (1 : ℝ) + 3 * (-3 / 2) < (1 + (-3 / 2)) ^ 3 :=
  one_add_mul_lt_pow_full (by norm_num) (by norm_num) (by norm_num)

/-- Boundary value `a = -2`: `1 + 3·(−2) = −5 < −1 = (1 − 2)³`. -/
example : (1 : ℝ) + 3 * (-2) < (1 + (-2)) ^ 3 :=
  one_add_mul_lt_pow_full (by norm_num) (by norm_num) (by norm_num)

/-- The `n = 2` case holds even at `a = -2`: `1 + 2·(−2) = −3 < 1 = (1−2)²`. -/
example : (1 : ℝ) + 2 * (-2) < (1 + (-2)) ^ 2 :=
  one_add_mul_lt_pow_full (by norm_num) (by norm_num) (by norm_num)

end BernoulliInequalityOQ01OQ01
