/-
  Erdős Problem #1: Distinct Subset Sums

  Source: https://erdosproblems.com/1
  Status: SOLVED
  Prize: $500

  Statement:
  If A ⊆ {1,...,N} with |A| = n and all 2^n subset sums are distinct,
  then N ≥ 2^(n-1).

  This is a classic result. The key insight is that if all subset sums
  are distinct, the maximum element must be at least 2^(n-1).

  More generally, Erdős asked about the constant c such that N ≥ c * 2^n.
-/

import Mathlib

open Finset

/-- A set has distinct subset sums if the sum function is injective on powersets -/
def hasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  Function.Injective fun S : Finset ℕ => S.filter (· ∈ A) |>.sum id

/-- Erdős Problem #1: If A ⊆ {1,...,N} has distinct subset sums, then N ≥ 2^(|A|-1) -/
theorem erdos_1_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N) (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card - 1) ≤ N := by
  sorry

/-- The maximum element of a set with distinct subset sums is at least 2^(n-1) -/
theorem max_element_bound {A : Finset ℕ} (hA : A.Nonempty)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card - 1) ≤ A.max' hA := by
  sorry

/-- Sidon-like property: consecutive sums differ -/
theorem subset_sums_spacing {A : Finset ℕ} (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A)
    (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) (hST : S ≠ T) :
    S.sum id ≠ T.sum id := by
  sorry
