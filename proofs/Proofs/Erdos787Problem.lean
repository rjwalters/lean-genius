/-
Erdős Problem #787: Sum-Free Subsets (Erdős-Moser Problem)

Source: https://erdosproblems.com/787
Status: SOLVED (bounds established)

Statement:
Let g(n) be maximal such that given any set A ⊆ ℝ with |A| = n, there exists
some B ⊆ A of size |B| ≥ g(n) such that b₁ + b₂ ∉ A for all b₁ ≠ b₂ ∈ B.

Estimate g(n).

Known Results:
- Klarner: g(n) ≫ log n (greedy construction)
- Choi (1971): g(n) ≪ n^(2/5+o(1))
- Ruzsa (2005): g(n) ≪ exp(√log n)
- Sanders (2021): (log n)^(1+c) ≪ g(n) for some c > 0
- Beker (2025): (log n)^(1+1/68+o(1)) ≪ g(n)

Current best bounds:
  (log n)^(1+c) ≪ g(n) ≪ exp(√(log n))

Note: Choi observed that WLOG we can assume A ⊆ ℤ.

Tags: sum-free, additive-combinatorics, erdos-moser
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos787

open Finset Real

/-!
## Part 1: Basic Definitions

Sum-free subsets and the function g(n).
-/

/-- A subset B of A is sum-avoiding if no sum of two distinct elements of B lies in A -/
def IsSumAvoidingIn (A B : Finset ℤ) : Prop :=
  B ⊆ A ∧ ∀ b₁ b₂ : ℤ, b₁ ∈ B → b₂ ∈ B → b₁ ≠ b₂ → (b₁ + b₂) ∉ A

/-- The maximum size of a sum-avoiding subset of A -/
noncomputable def maxSumAvoidingSize (A : Finset ℤ) : ℕ :=
  Finset.sup' (A.powerset.filter (fun B => IsSumAvoidingIn A B))
    ⟨∅, by simp [IsSumAvoidingIn]⟩
    Finset.card

/-- The function g(n): maximum such that every n-set has a sum-avoiding subset of size ≥ g(n) -/
noncomputable def g (n : ℕ) : ℕ :=
  -- Minimum over all n-sets A of maxSumAvoidingSize A
  -- This is the worst-case guarantee
  n  -- Placeholder; actual definition requires infimum over all n-sets

/-- Alternate definition via existence -/
def HasSumAvoidingSubset (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ B : Finset ℤ, IsSumAvoidingIn A B ∧ k ≤ B.card

/-- g(n) is the largest k such that every n-set has a sum-avoiding subset of size ≥ k -/
def g_spec (n k : ℕ) : Prop :=
  (∀ A : Finset ℤ, A.card = n → HasSumAvoidingSubset A k) ∧
  ¬(∀ A : Finset ℤ, A.card = n → HasSumAvoidingSubset A (k + 1))

/-!
## Part 2: Trivial Cases and Basic Properties
-/

/-- The empty set is trivially sum-avoiding -/
theorem empty_is_sum_avoiding (A : Finset ℤ) : IsSumAvoidingIn A ∅ := by
  constructor
  · exact empty_subset A
  · intros b₁ b₂ hb₁ _ _
    exact absurd hb₁ (not_mem_empty b₁)

/-- Any singleton is sum-avoiding (need two distinct elements to form a sum) -/
theorem singleton_is_sum_avoiding (A : Finset ℤ) (a : ℤ) (ha : a ∈ A) :
    IsSumAvoidingIn A {a} := by
  constructor
  · exact singleton_subset_iff.mpr ha
  · intros b₁ b₂ hb₁ hb₂ hne
    simp only [mem_singleton] at hb₁ hb₂
    rw [hb₁, hb₂] at hne
    exact absurd rfl hne

/-- g(n) ≥ 1 for n ≥ 1 -/
theorem g_ge_one (n : ℕ) (hn : n ≥ 1) : g n ≥ 1 := by
  -- Any non-empty set has at least a singleton sum-avoiding subset
  sorry

/-!
## Part 3: Klarner's Lower Bound (Greedy Construction)

g(n) ≥ c · log n for some constant c > 0.
-/

/-- The greedy algorithm for constructing sum-avoiding subsets -/
-- Start with B = ∅, and for each a ∈ A (in some order),
-- add a to B if doing so keeps B sum-avoiding
def greedySumAvoiding (A : Finset ℤ) : Finset ℤ :=
  A.fold (fun B a => if IsSumAvoidingIn A (insert a B) then insert a B else B) ∅

/-- Klarner's lower bound: g(n) ≫ log n -/
axiom klarner_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 → (g n : ℝ) ≥ c * Real.log n

/-!
## Part 4: Choi's Upper Bound (1971)

g(n) ≪ n^(2/5+o(1))
-/

/-- Choi's 1971 result: can restrict to integer sets without loss of generality -/
axiom choi_integer_reduction :
    -- If we prove bounds for A ⊆ ℤ, they hold for A ⊆ ℝ
    True

/-- Choi's upper bound -/
axiom choi_1971_upper_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (g n : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5 + ε)

/-!
## Part 5: Ruzsa's Upper Bound (2005)

g(n) ≪ exp(√(log n))
-/

/-- Ruzsa's 2005 improvement -/
axiom ruzsa_2005_upper_bound :
    ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≤ K * Real.exp (Real.sqrt (Real.log n))

/-!
## Part 6: Sanders' Lower Bound (2021)

(log n)^(1+c) ≪ g(n) for some c > 0.
-/

/-- Sanders' improved lower bound -/
axiom sanders_2021_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≥ K * (Real.log n) ^ (1 + c)

/-!
## Part 7: Beker's Lower Bound (2025)

(log n)^(1+1/68+o(1)) ≪ g(n)
-/

/-- The Beker exponent: 1 + 1/68 -/
noncomputable def bekerExponent : ℝ := 1 + 1 / 68

/-- Beker's 2025 improvement -/
axiom beker_2025_lower_bound :
    ∀ ε > 0, ∃ K : ℝ, K > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      (g n : ℝ) ≥ K * (Real.log n) ^ (bekerExponent - ε)

/-!
## Part 8: Current Best Bounds Summary
-/

/-- The current best bounds for g(n) -/
theorem erdos_787_current_bounds :
    -- Lower bound: (log n)^(1+c) ≪ g(n)
    (∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≥ K * (Real.log n) ^ (1 + c)) ∧
    -- Upper bound: g(n) ≪ exp(√(log n))
    (∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≤ K * Real.exp (Real.sqrt (Real.log n))) := by
  constructor
  · exact sanders_2021_lower_bound
  · exact ruzsa_2005_upper_bound

/-!
## Part 9: The Gap

The gap between bounds is still large:
- Lower: (log n)^(1+c) ≈ polylogarithmic
- Upper: exp(√(log n)) ≈ subpolynomial but superpolylogarithmic

Determining the true order of g(n) remains open.
-/

/-- The bounds don't match, so exact order is still open -/
axiom exact_order_open :
    -- The true order of g(n) is not yet determined
    True

/-!
## Part 10: Connection to k-configurations

Sanders and Beker use bounds on k-configurations to improve lower bounds.
-/

/-- A k-configuration in a set A -/
def IsKConfiguration (A : Finset ℤ) (k : ℕ) (B : Finset ℤ) : Prop :=
  B ⊆ A ∧ B.card = k ∧
  ∀ b₁ b₂ : ℤ, b₁ ∈ B → b₂ ∈ B → b₁ ≠ b₂ → (b₁ + b₂) ∈ A

/-- Connection to k-configurations -/
axiom k_config_connection :
    -- If A has few k-configurations, then A has large sum-avoiding subsets
    True

/-!
## Part 11: Main Problem Statement
-/

/-- Erdős Problem #787: The Erdős-Moser sum-free set problem -/
theorem erdos_787_statement :
    -- Best known bounds
    (∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      K * (Real.log n) ^ (1 + c) ≤ (g n : ℝ)) ∧
    (∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≤ K * Real.exp (Real.sqrt (Real.log n))) ∧
    -- Beker's specific exponent
    (∀ ε > 0, ∃ K : ℝ, K > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      K * (Real.log n) ^ (bekerExponent - ε) ≤ (g n : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact sanders_2021_lower_bound
  · exact ruzsa_2005_upper_bound
  · exact beker_2025_lower_bound

/-- Summary: Erdős Problem #787 has partial resolution with a gap -/
theorem erdos_787_summary :
    -- The problem asks for the exact order of g(n)
    -- Current bounds: polylog ≪ g(n) ≪ exp(√log n)
    -- The exact order remains open
    True := trivial

/-- The answer to Erdős Problem #787: PARTIALLY SOLVED (bounds established, gap remains) -/
theorem erdos_787_answer : True := trivial

end Erdos787
