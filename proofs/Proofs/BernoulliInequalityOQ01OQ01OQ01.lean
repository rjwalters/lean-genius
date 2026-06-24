import Mathlib

/-
# Sharp Left Endpoint of the Strict Bernoulli Inequality

**Open question (bernoulli-inequality-oq-01-oq-01).** The parent entry
`bernoulli-inequality-oq-01-oq-01` (`BernoulliInequalityOQ01OQ01.lean`) proved the
*strict* Bernoulli inequality `1 + n·a < (1 + a)ⁿ` on the entire weak domain
`-2 ≤ a` (for `a ≠ 0`, `n ≥ 2`), matching the reach of Mathlib's
`one_add_mul_le_pow`. It closed by asking:

> *Is `-2` the true left endpoint of the strict inequality for fixed `n`, or does
> the admissible range depend on `n` (e.g. does some `n` admit `a < -2`)?*

**Answer: `-2` is NOT the left endpoint for any fixed `n`; the admissible range
depends on the parity of `n`.** This file proves the four facts that pin it down.

* `strict_even` — for **even** `n ≥ 2` and every `a ≠ 0`, `1 + n·a < (1 + a)ⁿ`.
  There is *no* left endpoint at all: when `a < -1` the right side is a positive
  even power while the left side is negative.
* `cubic_iff` — for `n = 3` the strict inequality holds **iff** `a ≠ 0 ∧ -3 < a`,
  because `(1+a)³ - (1+3a) = a²(a+3)`. The left endpoint is exactly `-3`, strictly
  below `-2`.
* `exists_lt_neg_two_strict` — consequently some `n` (e.g. `n = 3`, `a = -5/2`)
  *does* admit `a < -2`, answering the parenthetical sub-question affirmatively.
* `sharp_uniform` — `-2` is nonetheless sharp as the **uniform** (`n`-independent)
  left endpoint: `(∀ n, 1 + n·a ≤ (1 + a)ⁿ) ↔ -2 ≤ a`. The forward direction is
  Mathlib's `one_add_mul_le_pow`; the reverse direction shows that for every
  `a < -2` some *odd* exponent violates the inequality, via a second-order
  (quadratic) Bernoulli lower bound proved here as `quad_bernoulli`.

**Why parity is the whole story.** For even `n`, `(1+a)ⁿ ≥ 0` everywhere, so the
inequality is automatic once `1 + n·a < 0` (i.e. `a < -1`). For odd `n`, `(1+a)ⁿ`
turns negative for `a < -1` and, being a degree-`n` power, eventually outruns the
line `1 + n·a` downward — but only past a finite endpoint `a_n^* < -2` that creeps
up toward `-2` as `n → ∞` (e.g. `a_3^* = -3`). Thus `-2 = sup_n a_n^*` is approached
but never attained by any single `n`, which is exactly why it is the sharp uniform
bound while being the endpoint of *no* individual `n`.

This complements Mathlib (`one_add_mul_le_pow`, weak, `-2 ≤ a`) and the parent
(strict, `-2 ≤ a`): neither addresses the per-`n` admissible range or the
sharpness/optimality of the constant `-2`.
-/

namespace BernoulliInequalityOQ01OQ01OQ01

variable {a x : ℝ}

/-- Strict Bernoulli on the positive-factor range `a > -1`, by the standard
`Nat.le_induction` (the inductive estimate is multiplied by `1 + a > 0`). Re-proved
here to keep the file self-contained. -/
theorem strict_pos (ha : -1 < a) (ha0 : a ≠ 0) :
    ∀ {n : ℕ}, 2 ≤ n → 1 + (n : ℝ) * a < (1 + a) ^ n := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => push_cast; nlinarith [ha2]
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

/-- **Even exponents have no left endpoint.** For every even `n ≥ 2` and every
`a ≠ 0`, the strict Bernoulli inequality holds — even far below `-2`. For `a < -1`
the right-hand side is a positive even power while the left-hand side is negative. -/
theorem strict_even {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) (ha0 : a ≠ 0) :
    1 + (n : ℝ) * a < (1 + a) ^ n := by
  rcases lt_or_ge a (-1) with hlt | hge
  · -- `a < -1`: `(1+a)ⁿ > 0` (even power, nonzero base) while `1 + n·a < 0`.
    have hb : (1 + a) ≠ 0 := by intro h; linarith
    have hpos : 0 < (1 + a) ^ n := hn.pow_pos hb
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hna : (n : ℝ) * a ≤ -(n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith [this]
    have : 1 + (n : ℝ) * a < 0 := by linarith
    linarith
  · rcases eq_or_lt_of_le hge with heq | hgt
    · -- `a = -1`: `(1+a)ⁿ = 0` while `1 + n·a = 1 - n ≤ -1`.
      have hae : a = -1 := heq.symm
      subst hae
      have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      rw [show (1 : ℝ) + -1 = 0 by norm_num, zero_pow (show n ≠ 0 by omega)]
      linarith
    · exact strict_pos hgt ha0 hn2

/-- **The cubic case has left endpoint exactly `-3`.** For `n = 3`, strict Bernoulli
holds **iff** `a ≠ 0 ∧ -3 < a`, since `(1+a)³ - (1+3a) = a²(a+3)`. In particular the
endpoint `-3` is strictly below `-2`. -/
theorem cubic_iff : 1 + 3 * a < (1 + a) ^ 3 ↔ a ≠ 0 ∧ -3 < a := by
  have hid : (1 + a) ^ 3 - (1 + 3 * a) = a ^ 2 * (a + 3) := by ring
  constructor
  · intro h
    have key : 0 < a ^ 2 * (a + 3) := by linarith [hid]
    refine ⟨?_, ?_⟩
    · rintro rfl; norm_num at h
    · nlinarith [sq_nonneg a, key]
  · rintro ⟨ha0, ha3⟩
    have ha2 : 0 < a ^ 2 := by positivity
    have : 0 < a ^ 2 * (a + 3) := mul_pos ha2 (by linarith)
    linarith [hid]

/-- **Some exponent admits `a < -2`.** Concretely `n = 3`, `a = -5/2`: this answers
the parenthetical sub-question of the open problem affirmatively. -/
theorem exists_lt_neg_two_strict :
    ∃ (a : ℝ) (n : ℕ), a < -2 ∧ 1 + (n : ℝ) * a < (1 + a) ^ n := by
  refine ⟨-5 / 2, 3, by norm_num, ?_⟩
  push_cast; norm_num

/-- **Second-order (quadratic) Bernoulli bound.** For `x ≥ 0` and every `n`,
`1 + n·x + C(n,2)·x² ≤ (1 + x)ⁿ`. The quadratic term is what lets a power beat a
line; the first-order bound `one_add_mul_le_pow` is too weak for the sharpness
argument below. -/
theorem quad_bernoulli (hx : 0 ≤ x) (n : ℕ) :
    1 + (n : ℝ) * x + ((n : ℝ) * ((n : ℝ) - 1) / 2) * x ^ 2 ≤ (1 + x) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1x : (0 : ℝ) ≤ 1 + x := by linarith
      have hstep := mul_le_mul_of_nonneg_right ih h1x
      have hkk : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · simp [hk]
        · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith
      have hx3 : (0 : ℝ) ≤ ((k : ℝ) * ((k : ℝ) - 1) / 2) * x ^ 3 :=
        mul_nonneg (by linarith) (pow_nonneg hx 3)
      rw [pow_succ (1 + x) k]
      push_cast
      nlinarith [hstep, hx3]

/-- **`-2` is the sharp uniform left endpoint.** Bernoulli's inequality holds for
*every* exponent simultaneously exactly on `-2 ≤ a`:
`(∀ n, 1 + n·a ≤ (1 + a)ⁿ) ↔ -2 ≤ a`. The forward direction is Mathlib's
`one_add_mul_le_pow`; the reverse shows every `a < -2` is violated by some odd
exponent, using the quadratic Bernoulli bound to make a power outrun the line. -/
theorem sharp_uniform :
    (∀ n : ℕ, 1 + (n : ℝ) * a ≤ (1 + a) ^ n) ↔ -2 ≤ a := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    -- `hlt : a < -2`.  Set `s = -(1+a) > 1`, `c = s - 1 > 0`.
    set s : ℝ := -1 - a with hs
    have hs1 : 1 < s := by rw [hs]; linarith
    set c : ℝ := s - 1 with hc
    have hc0 : 0 < c := by rw [hc]; linarith
    have hc2 : 0 < c ^ 2 := pow_pos hc0 2
    have h4c : 0 < 4 / c ^ 2 := div_pos (by norm_num) hc2
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / c ^ 2)
    have hNpos : 0 < N := by
      have : (0 : ℝ) < (N : ℝ) := lt_trans h4c hN
      exact_mod_cast this
    set n : ℕ := 2 * N + 1 with hn
    have hodd : Odd n := ⟨N, by omega⟩
    have hn3 : 3 ≤ n := by omega
    have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    -- `4 < n · c²`.
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show N ≤ n by omega)
    have hnN : 4 / c ^ 2 < (n : ℝ) := by linarith
    have hnc : (4 : ℝ) < (n : ℝ) * c ^ 2 := (div_lt_iff₀ hc2).mp hnN
    -- Quadratic Bernoulli bound, transported to `s = 1 + c`.
    have hsc : s = 1 + c := by rw [hc]; ring
    have hb : 1 + (n : ℝ) * c + ((n : ℝ) * ((n : ℝ) - 1) / 2) * c ^ 2 ≤ s ^ n := by
      have := quad_bernoulli hc0.le n
      rwa [← hsc] at this
    have hns : (n : ℝ) * s = (n : ℝ) * (1 + c) := by rw [hsc]
    have hfac : 0 < ((n : ℝ) - 1) * ((n : ℝ) * c ^ 2 - 4) :=
      mul_pos (by linarith) (by linarith)
    have hsn : (n : ℝ) * s + (n : ℝ) - 1 < s ^ n := by nlinarith [hb, hns, hfac]
    -- Evaluate at the odd exponent and derive the contradiction.
    have hbase : (1 + a) = -s := by rw [hs]; ring
    have hop : (1 + a) ^ n = -(s ^ n) := by rw [hbase, hodd.neg_pow]
    have hla : 1 + (n : ℝ) * a = 1 - (n : ℝ) - (n : ℝ) * s := by rw [hs]; ring
    have hcontra := h n
    rw [hop, hla] at hcontra
    linarith [hsn, hcontra]
  · intro ha n
    exact one_add_mul_le_pow ha n

end BernoulliInequalityOQ01OQ01OQ01
