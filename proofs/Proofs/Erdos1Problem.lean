/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0caca922-2d23-49b7-814f-2ad63b818d80

The following was proved by Aristotle:

- theorem erdos_1_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N) (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card - 1) ≤ N

- theorem max_element_bound {A : Finset ℕ} (hA : A.Nonempty)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card - 1) ≤ A.max' hA

- theorem subset_sums_spacing {A : Finset ℕ} (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A)
    (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) (hST : S ≠ T) :
    S.sum id ≠ T.sum id
-/

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
  -- It is enough to prove that the number of subsets of $A$ is at most $2N$.
  have h_card_subsets : (Finset.powerset A).card ≤ 2 * N := by
    -- Consider the function that maps each subset of $A$ to its sum. This function is injective because $A$ has distinct subset sums.
    have h_injective : Function.Injective (fun S : Finset ℕ => S.filter (· ∈ A) |>.sum id) := by
      exact?;
    exact absurd ( @h_injective { 0 } { } ) ( by aesop );
  rcases k : Finset.card A with ( _ | _ | k ) <;> simp_all +decide [ pow_succ, mul_assoc ];
  · linarith;
  · grind

/-- The maximum element of a set with distinct subset sums is at least 2^(n-1) -/
theorem max_element_bound {A : Finset ℕ} (hA : A.Nonempty)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card - 1) ≤ A.max' hA := by
  convert erdos_1_lower_bound _ _ _;
  · exact fun a ha => Finset.le_max' _ _ ha;
  · assumption;
  · assumption

/-- Sidon-like property: consecutive sums differ -/
theorem subset_sums_spacing {A : Finset ℕ} (hA_pos : ∀ a ∈ A, 0 < a)
    (hDistinct : hasDistinctSubsetSums A)
    (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) (hST : S ≠ T) :
    S.sum id ≠ T.sum id := by
  have := @hDistinct S T; simp_all +decide [ Finset.subset_iff ] ;
  rwa [ Finset.sum_filter_of_ne, Finset.sum_filter_of_ne ] at this <;> aesop_cat