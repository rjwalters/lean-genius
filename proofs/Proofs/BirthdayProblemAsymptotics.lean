import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Birthday Problem: Collision Asymptotics

## What This Proves

The birthday problem asks: with k people choosing from n equally likely birthdays,
what is the probability that all birthdays are distinct?

**Exact formula**: P(all distinct) = ∏_{i=0}^{k-1} (1 - i/n)

**Asymptotic upper bound** (PROVED):
  ∏_{i=0}^{k-1} (1 - i/n) ≤ exp(-k(k-1)/(2n))

using the fundamental inequality 1 - x ≤ exp(-x).

**Significance**: The collision probability 1 - ∏(1-i/n) ≥ 1 - exp(-k(k-1)/(2n)),
giving the threshold k ≈ √(2n·ln 2) ≈ 1.177√n for 50% collision probability.
For n = 365: k ≈ 22.5, explaining the "23 people" result.

## Status
- 0 axioms, 0 sorries
- All theorems fully proved from Mathlib
-/

open Real Finset BigOperators

namespace BirthdayAsymptotics

/-- 1 - x ≤ exp(-x) for all x. From exp(t) ≥ 1 + t (set t = -x). -/
theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  linarith [add_one_le_exp (-x)]

/-- ∏_{i∈range k} (1 - i/n) ≤ exp(-∑_{i∈range k} i/n) when k ≤ n. -/
theorem prod_one_sub_le_exp {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n) ≤
      Real.exp (- ∑ i ∈ Finset.range k, ((i : ℝ) / n)) := by
  -- Convert sum in exp to product of exp
  conv_rhs => rw [← Finset.sum_neg_distrib]
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    rw [Finset.mem_range] at hi
    have : (i : ℝ) / n ≤ 1 := by
      rw [div_le_one (by positivity : (n : ℝ) > 0)]
      exact Nat.cast_le.mpr (Nat.lt_of_lt_of_le hi hk |>.le)
    linarith
  · intro i _
    exact one_sub_le_exp_neg (i / n)

/-- Gauss's formula: ∑_{i=0}^{k-1} i = k(k-1)/2 (over ℝ). -/
theorem sum_range_eq (k : ℕ) :
    ∑ i ∈ Finset.range k, (i : ℝ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Birthday Collision Upper Bound** (PROVED, 0 axioms, 0 sorries)

∏_{i=0}^{k-1} (1 - i/n) ≤ exp(-k(k-1)/(2n))

Each factor 1-i/n ≤ exp(-i/n), multiply all factors, use ∑i/n = k(k-1)/(2n). -/
theorem birthday_collision_upper_bound {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n) ≤
      Real.exp (-(↑k * (↑k - 1) / (2 * ↑n))) := by
  have h1 := prod_one_sub_le_exp hn k hk
  have h2 : (∑ i ∈ Finset.range k, ((i : ℝ) / n)) = ↑k * (↑k - 1) / (2 * ↑n) := by
    rw [← Finset.sum_div, sum_range_eq]; ring
  linarith [Real.exp_le_exp_of_le (by linarith [h2] : -(∑ i ∈ Finset.range k, ((i : ℝ) / n)) ≤ -(↑k * (↑k - 1) / (2 * ↑n))), h1]

/-- **Collision probability lower bound**: P(collision) ≥ 1 - exp(-k(k-1)/(2n)). -/
theorem collision_prob_lower_bound {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    1 - ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n) ≥
      1 - Real.exp (-(↑k * (↑k - 1) / (2 * ↑n))) := by
  linarith [birthday_collision_upper_bound hn k hk]

end BirthdayAsymptotics
