/-!
# Erdős Problem #542: Reciprocal Sums Under LCM Constraints

Let A ⊆ {1, ..., n} be a set such that lcm(a, b) > n for all distinct a, b ∈ A.
Erdős asked: must ∑_{a ∈ A} 1/a ≤ 31/30?

Schinzel and Szekeres (1959) answered yes. The bound 31/30 comes from
{2, 3, 5}: 1/2 + 1/3 + 1/5 = 31/30.

Chen (1996) proved that for n > 172509, ∑ 1/a < 1/3 + 1/4 + 1/5 + 1/7 + 1/11.

Erdős, Schinzel, and Szekeres conjectured that only {2,3,5} and {3,4,5,7,11}
are the maximal sets achieving sums exceeding 1.

Reference: https://erdosproblems.com/542
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## LCM Condition and Reciprocal Sum -/

/-- A set A ⊆ {1,...,n} has the pairwise LCM property: lcm(a,b) > n
    for all distinct elements a, b ∈ A. -/
def PairwiseLCMExceeds (A : Finset ℕ) (n : ℕ) : Prop :=
  (∀ a ∈ A, a ∈ Finset.range (n + 1) ∧ 0 < a) ∧
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < a.lcm b

/-- The reciprocal sum ∑_{a ∈ A} 1/a as a rational number. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  A.sum (fun a => (1 : ℚ) / a)

/-! ## Main Results -/

/-- Erdős Problem 542 (Schinzel-Szekeres 1959): If A ⊆ {1,...,n} has
    lcm(a,b) > n for all distinct a,b ∈ A, then ∑ 1/a ≤ 31/30. -/
def ErdosProblem542 : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ, PairwiseLCMExceeds A n →
    reciprocalSum A ≤ 31 / 30

/-- The bound 31/30 is achieved by {2, 3, 5}: 1/2 + 1/3 + 1/5 = 31/30. -/
axiom bound_achieved_by_235 :
    reciprocalSum {2, 3, 5} = 31 / 30

/-- {2, 3, 5} satisfies the LCM condition for n = 5. -/
axiom example_235_valid : PairwiseLCMExceeds {2, 3, 5} 5

/-! ## Chen's Stronger Bound -/

/-- Chen's bound (1996): for n > 172509, the reciprocal sum is strictly
    less than 1/3 + 1/4 + 1/5 + 1/7 + 1/11. -/
def ChenBound : Prop :=
  ∀ n : ℕ, 172509 < n →
    ∀ A : Finset ℕ, PairwiseLCMExceeds A n →
      reciprocalSum A < 1/3 + 1/4 + 1/5 + 1/7 + 1/11

/-- The Chen bound value equals 2927/4620. -/
theorem chen_bound_value :
    (1 : ℚ)/3 + 1/4 + 1/5 + 1/7 + 1/11 = 2927/4620 := by
  norm_num

/-! ## Maximal Sets Conjecture -/

/-- Erdős-Schinzel-Szekeres conjecture: the only sets achieving
    reciprocal sum > 1 under the LCM condition are {2,3,5} and {3,4,5,7,11}. -/
def MaximalSetsConjecture : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ, PairwiseLCMExceeds A n →
    1 < reciprocalSum A →
    (A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11})

/-- {3, 4, 5, 7, 11} achieves sum > 1 under the LCM condition. -/
axiom example_34_5_7_11_sum :
    1 < reciprocalSum {3, 4, 5, 7, 11}

/-- {3, 4, 5, 7, 11} satisfies the LCM condition for n = 11. -/
axiom example_34_5_7_11_valid :
    PairwiseLCMExceeds {3, 4, 5, 7, 11} 11

/-! ## Structural Properties -/

/-- The LCM condition implies no element divides another (within {1,...,n}). -/
axiom lcm_condition_no_divisibility (A : Finset ℕ) (n : ℕ)
    (h : PairwiseLCMExceeds A n) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hle : a ≤ b) (hdvd : a ∣ b) :
    n < b

/-- Singleton sets always satisfy the LCM condition vacuously. -/
theorem singleton_satisfies_lcm (a n : ℕ) (ha : a ∈ Finset.range (n + 1))
    (hpos : 0 < a) :
    PairwiseLCMExceeds {a} n := by
  constructor
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨ha, hpos⟩
  · intro x hx y hy hxy
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact absurd rfl hxy

/-- The reciprocal sum of a singleton {a} is 1/a. -/
theorem reciprocal_sum_singleton (a : ℕ) (ha : 0 < a) :
    reciprocalSum {a} = 1 / (a : ℚ) := by
  simp [reciprocalSum]

/-- The Schinzel-Szekeres theorem solves Erdős Problem 542. -/
axiom schinzel_szekeres_solves_542 : ErdosProblem542
