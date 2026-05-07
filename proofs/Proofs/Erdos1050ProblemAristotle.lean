/-
  Aristotle targets for Erdős Problem #1050: Irrationality of ∑ 1/(2^n - 3)
  Routine supporting lemmas for automated proof search.
  See Erdos1050Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main irrationality result (Borwein 1991) or transcendence conjecture
  - Routine: arithmetic about 2^n ± 3, convergence setup, logical implications
  - Transcendence → irrationality (follows from Mathlib's Transcendental.irrational)
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace Erdos1050Aristotle

open BigOperators Real Filter Topology

/-
## Section 1: Arithmetic of 2^n ± r

These are used to verify the non-pole conditions.
-/

/-- 2^n ≥ 2 for n ≥ 1. -/
theorem two_pow_ge_two (n : ℕ) (hn : n ≥ 1) : 2 ≤ 2 ^ n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- 2^n ≥ 4 for n ≥ 2. -/
theorem two_pow_ge_four (n : ℕ) (hn : n ≥ 2) : 4 ≤ 2 ^ n := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- (2 : ℝ)^n ≥ 2 for n ≥ 1. -/
theorem two_pow_real_ge_two (n : ℕ) (hn : n ≥ 1) : (2 : ℝ) ^ n ≥ 2 := by
  have h := two_pow_ge_two n hn
  exact_mod_cast h

/-- (2 : ℝ)^n ≥ 4 for n ≥ 2. -/
theorem two_pow_real_ge_four (n : ℕ) (hn : n ≥ 2) : (2 : ℝ) ^ n ≥ 4 := by
  have h := two_pow_ge_four n hn
  exact_mod_cast h

/-- (2 : ℝ)^n > 0 for all n. -/
theorem two_pow_real_pos (n : ℕ) : (0 : ℝ) < 2 ^ n :=
  pow_pos (by norm_num) n

/-- 2^1 = 2. -/
theorem two_pow_one : (2 : ℝ) ^ 1 = 2 := by norm_num

/-- 2^1 - 3 = -1 (used for the n=1 pole check). -/
theorem two_pow_one_sub_three : (2 : ℝ) ^ 1 - 3 = -1 := by norm_num

/-- For n ≥ 2, (2 : ℝ)^n > 3, so 2^n - 3 ≠ 0. -/
theorem two_pow_sub_three_ne_zero (n : ℕ) (hn : n ≥ 2) : (2 : ℝ) ^ n - 3 ≠ 0 := by
  have h : (2 : ℝ) ^ n ≥ 4 := two_pow_real_ge_four n hn
  linarith

/-- For n ≥ 2, (2 : ℝ)^n - 3 > 0. -/
theorem two_pow_sub_three_pos (n : ℕ) (hn : n ≥ 2) : 0 < (2 : ℝ) ^ n - 3 := by
  have h : (2 : ℝ) ^ n ≥ 4 := two_pow_real_ge_four n hn
  linarith

/-- 2^n ≠ 3 for all n : the non-pole condition for r = -3. -/
theorem two_pow_ne_three (n : ℕ) : (2 : ℝ) ^ n ≠ 3 := by
  intro h
  have := two_pow_real_pos n
  cases Nat.lt_or_ge n 2 with
  | inl hn =>
    interval_cases n
    · norm_num at h
    · norm_num at h
  | inr hn =>
    have h4 : (2 : ℝ) ^ n ≥ 4 := two_pow_real_ge_four n hn
    linarith

/-- 2^n ≠ 1 for n ≥ 1 : the non-pole condition for r = -1. -/
theorem two_pow_ne_one (n : ℕ) (hn : n ≥ 1) : (2 : ℝ) ^ n ≠ 1 := by
  have h2 : (2 : ℝ) ^ n ≥ 2 := two_pow_real_ge_two n hn
  linarith

/-- The denominator 2^n + r is nonzero when r ≠ -2^n. -/
theorem denom_pos_when_no_pole (q : ℕ) (r : ℝ) (hq : q ≥ 2) (n : ℕ) (hn : n ≥ 1)
    (hpole : r ≠ -((q : ℝ) ^ n)) : (q : ℝ) ^ n + r ≠ 0 := by
  intro h
  apply hpole
  linarith

/-
## Section 2: Concrete Series Values

First few terms of the series ∑ 1/(2^n - 3).
-/

/-- 1/(2^2 - 3) = 1/1 = 1. -/
theorem term_at_2 : 1 / ((2 : ℝ) ^ 2 - 3) = 1 := by norm_num

/-- 1/(2^3 - 3) = 1/5. -/
theorem term_at_3 : 1 / ((2 : ℝ) ^ 3 - 3) = 1 / 5 := by norm_num

/-- 1/(2^4 - 3) = 1/13. -/
theorem term_at_4 : 1 / ((2 : ℝ) ^ 4 - 3) = 1 / 13 := by norm_num

/-- 1/(2^5 - 3) = 1/29. -/
theorem term_at_5 : 1 / ((2 : ℝ) ^ 5 - 3) = 1 / 29 := by norm_num

/-- 2^1 - 3 = -1, 2^2 - 3 = 1. -/
theorem denom_n1_n2 : (2 : ℤ) ^ 1 - 3 = -1 ∧ (2 : ℤ) ^ 2 - 3 = 1 := by norm_num

/-
## Section 3: Summability Helpers

Tools for proving series convergence by comparison.
-/

/-- For q ≥ 2 and n ≥ 1, q^n ≥ q > 1. -/
theorem q_pow_gt_one (q : ℕ) (n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    (1 : ℝ) < (q : ℝ) ^ n := by
  have hq_gt : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  exact one_lt_pow_of_one_lt_of_ne_zero hq_gt (by omega)

/-- |1/(2^n - 3)| ≤ 2/2^n for n ≥ 3 (comparison for convergence). -/
theorem abs_term_bound (n : ℕ) (hn : n ≥ 3) :
    |1 / ((2 : ℝ) ^ n - 3)| ≤ 2 / (2 : ℝ) ^ n := by
  -- 2^n ≥ 8 for n ≥ 3, so 2^n - 3 ≥ 5 > 0
  have h8 : (8 : ℝ) ≤ 2 ^ n :=
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right (by norm_num) hn
  have hpos : 0 < (2 : ℝ) ^ n - 3 := by linarith
  rw [abs_of_pos (div_pos one_pos hpos), div_le_div_iff hpos (two_pow_real_pos n)]
  -- goal: 1 * 2^n ≤ 2 * (2^n - 3), i.e., 6 ≤ 2^n
  linarith

/-- The geometric series ∑ 1/2^n converges. -/
theorem inv_two_pow_summable :
    Summable (fun n : ℕ => (1 : ℝ) / 2 ^ n) := by
  apply Summable.congr (summable_geometric_of_lt_one (by norm_num) (by norm_num : 1/2 < 1))
  intro n; simp [one_div, pow_succ]

/-
## Section 4: Transcendence → Irrationality

The logical step: transcendental implies irrational.
-/

/-- If x is transcendental over ℚ, then x is irrational. -/
theorem transcendental_implies_irrational (x : ℝ) (h : Transcendental ℚ x) : Irrational x :=
  Transcendental.irrational h

/-- Transcendental numbers are not rational. -/
theorem transcendental_not_rational (x : ℝ) (h : Transcendental ℚ x) : x ∉ Set.range ((↑) : ℚ → ℝ) := by
  intro ⟨q, hq⟩
  exact h (hq ▸ isAlgebraic_algebraMap q)

/-
## Section 5: Geometric Series for Comparison

Used when proving summability by comparison with geometric series.
-/

/-- For q ≥ 2, 1/q^n → 0. -/
theorem inv_q_pow_tendsto_zero (q : ℕ) (hq : q ≥ 2) :
    Tendsto (fun n : ℕ => (1 : ℝ) / (q : ℝ) ^ n) atTop (nhds 0) := by
  have hq_gt : (1 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_pred hq
  have : Tendsto (fun n : ℕ => ((1 : ℝ) / q) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  simpa [div_pow]

/-- For q ≥ 2, ∑ 1/q^n is summable. -/
theorem inv_q_pow_summable (q : ℕ) (hq : q ≥ 2) :
    Summable (fun n : ℕ => (1 : ℝ) / (q : ℝ) ^ n) := by
  apply summable_of_summable_norm
  simp only [norm_div, norm_pow, Real.norm_ofNat]
  apply Summable.congr (summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one (by exact_mod_cast (show 0 < q by omega))];
        exact_mod_cast (show 1 < q by omega)))
  intro n; simp [div_pow]

/-
## Section 6: Utility Lemmas
-/

/-- r + (-r) = 0 for any r : ℝ. -/
theorem add_neg_self (r : ℝ) : r + (-r) = 0 := add_neg_cancel r

/-- q^n + r ≠ 0 when r > 0 and q ≥ 2. -/
theorem q_pow_add_pos_ne_zero (q : ℕ) (n : ℕ) (hq : q ≥ 2) (r : ℝ) (hr : r > 0) :
    (q : ℝ) ^ n + r ≠ 0 := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_pred hq
  have := pow_pos hq_pos n
  linarith

/-- For large n, 1/(q^n + r) is eventually small. -/
theorem inv_q_pow_plus_r_tendsto_zero (q : ℕ) (r : ℝ) (hq : q ≥ 2)
    (hpole : ∀ n : ℕ, (q : ℝ) ^ n + r ≠ 0) :
    Tendsto (fun n : ℕ => 1 / ((q : ℝ) ^ n + r)) atTop (nhds 0) := by
  have hq_gt : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  -- q^n + r → +∞ since q^n → +∞ and r is fixed
  have hqn_atTop : Tendsto (fun n : ℕ => (q : ℝ) ^ n + r) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    have hb := (Filter.tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hq_gt)) (b - r)
    filter_upwards [hb] with n hn
    linarith
  -- 1/(q^n + r) = (q^n + r)⁻¹ → 0 by composing with inv → 0
  rw [show (fun n : ℕ => 1 / ((q : ℝ) ^ n + r)) = (fun n => ((q : ℝ) ^ n + r)⁻¹) from by
    ext n; simp [one_div]]
  exact tendsto_inv_atTop_zero.comp hqn_atTop

/-- 2 is not 0, useful for division. -/
theorem two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num

/-- For q ≥ 2, q is not 0 as a real. -/
theorem q_ne_zero (q : ℕ) (hq : q ≥ 2) : (q : ℝ) ≠ 0 := by
  exact_mod_cast (show q ≠ 0 by omega)

end Erdos1050Aristotle
