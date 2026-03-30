/-
Erdős Problem #787: Sum-Free Subsets (Erdős-Moser Problem)

Source: https://erdosproblems.com/787
Status: OPEN (exact order unknown)

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

/- ## Part 1: Basic Definitions -/

/-- A subset B of A is sum-avoiding if no sum of two distinct elements of B lies in A -/
def IsSumAvoidingIn (A B : Finset ℤ) : Prop :=
  B ⊆ A ∧ ∀ b₁ b₂ : ℤ, b₁ ∈ B → b₂ ∈ B → b₁ ≠ b₂ → (b₁ + b₂) ∉ A

/-- The maximum size of a sum-avoiding subset of A -/
noncomputable def maxSumAvoidingSize (A : Finset ℤ) : ℕ :=
  Finset.sup' (A.powerset.filter (fun B => IsSumAvoidingIn A B))
    ⟨∅, by simp [IsSumAvoidingIn]⟩
    Finset.card

/-- There exists a sum-avoiding subset of A of size ≥ k -/
def HasSumAvoidingSubset (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ B : Finset ℤ, IsSumAvoidingIn A B ∧ k ≤ B.card

/-- g(n) is the largest k such that every n-set has a sum-avoiding subset of size ≥ k.
    Axiomatized since the definition requires infimum over all n-element integer sets. -/
axiom g (n : ℕ) : ℕ

/-- Specification: g(n) is the largest k with the universal property -/
/- ## Part 2: Trivial Cases -/

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

/- ## Part 3: Klarner's Lower Bound -/

/-- Klarner's lower bound: g(n) ≫ log n via greedy construction -/
/- ## Part 4: Choi's Upper Bound (1971) -/

/-- Choi's upper bound: g(n) ≪ n^(2/5+o(1)) -/
/- ## Part 5: Ruzsa's Upper Bound (2005) -/

/-- Ruzsa's 2005 improvement: g(n) ≪ exp(√(log n)) — the current best upper bound -/
axiom ruzsa_2005_upper_bound :
    ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≤ K * Real.exp (Real.sqrt (Real.log n))

/- ## Part 6: Sanders' Lower Bound (2021) -/

/-- Sanders' improved lower bound: (log n)^(1+c) ≪ g(n) for some c > 0 -/
axiom sanders_2021_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≥ K * (Real.log n) ^ (1 + c)

/- ## Part 7: Beker's Lower Bound (2025) -/

/-- The Beker exponent: 1 + 1/68 -/
noncomputable def bekerExponent : ℝ := 1 + 1 / 68

/-- Beker's 2025 improvement: (log n)^(1+1/68-ε) ≪ g(n) -/
axiom beker_2025_lower_bound :
    ∀ ε > 0, ∃ K : ℝ, K > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      (g n : ℝ) ≥ K * (Real.log n) ^ (bekerExponent - ε)

/- ## Part 8: k-Configurations -/

/-- A k-configuration in a set A: B ⊆ A with |B| = k where all pairwise sums lie in A -/
def IsKConfiguration (A : Finset ℤ) (k : ℕ) (B : Finset ℤ) : Prop :=
  B ⊆ A ∧ B.card = k ∧
  ∀ b₁ b₂ : ℤ, b₁ ∈ B → b₂ ∈ B → b₁ ≠ b₂ → (b₁ + b₂) ∈ A

/- ## Part 9: Summary -/

/-- **Summary of Erdős Problem #787:**

PROBLEM: Estimate g(n), the worst-case size of a sum-avoiding subset
in any n-element integer set.

CURRENT BEST BOUNDS:
- Lower: (log n)^(1+c) (Sanders 2021), refined to (log n)^(1+1/68-ε) (Beker 2025)
- Upper: exp(√(log n)) (Ruzsa 2005)

The exact order of g(n) remains a major open problem in additive combinatorics.

This theorem packages: Sanders lower bound, Ruzsa upper bound, and Beker's refinement. -/
theorem erdos_787_summary :
    (∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≥ K * (Real.log n) ^ (1 + c)) ∧
    (∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (g n : ℝ) ≤ K * Real.exp (Real.sqrt (Real.log n))) ∧
    (∀ ε > 0, ∃ K : ℝ, K > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      (g n : ℝ) ≥ K * (Real.log n) ^ (bekerExponent - ε)) :=
  ⟨sanders_2021_lower_bound, ruzsa_2005_upper_bound, beker_2025_lower_bound⟩

end Erdos787
