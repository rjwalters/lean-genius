/-
  Erdős Problem #1, Open Question 01:
  Does N ≥ c · 2^n hold for some absolute constant c > 0?

  If A ⊆ {1,...,N} has n elements and all 2^n subset sums are distinct,
  must N ≥ c · 2^n? This is Erdős's $500 conjecture.

  Best known bounds:
  - Lower: N ≥ √(2/π) · 2^n / √n (Dubroff-Fox-Xu 2021)
  - Upper (Conway-Guy): minimum N ≤ 0.22009 · 2^n

  This file extends Erdos1Problem.lean with:
  1. A tighter sum bound: sum(A) ≥ 2^n - 1
  2. Monotonicity: subsets of DSS sets have DSS
  3. Recovery of the counting bound as a corollary of the sum bound
  4. Small case verifications

  Status: OPEN ($500 prize)
  Reference: https://erdosproblems.com/1
-/

import Proofs.Erdos1Problem
import Mathlib

open Finset

/- ## Part I: Sum Bound -/

/-- The total sum of a set with distinct subset sums is at least 2^n - 1.
    This is tighter than the element-wise counting bound since sum(A) ≤ n · max(A).
    Proof: the 2^n distinct sums are non-negative integers in [0, sum(A)],
    so sum(A) + 1 ≥ 2^n. -/
theorem distinct_subset_sums_sum_bound {A : Finset ℕ}
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.sum id + 1 := by
  have hinj : Set.InjOn (fun (S : Finset ℕ) => S.sum id)
      (↑A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
    exact hDistinct S T hS hT heq
  have himg_card : (A.powerset.image (fun S => S.sum id)).card =
      2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  have himg_sub : A.powerset.image (fun S => S.sum id) ⊆
      Finset.range (A.sum id + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, hSmem, rfl⟩ := hx
    rw [Finset.mem_powerset] at hSmem
    rw [Finset.mem_range]
    suffices S.sum id ≤ A.sum id by omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hSmem
      (fun _ _ _ => Nat.zero_le _)
  calc 2 ^ A.card
    = (A.powerset.image (fun S => S.sum id)).card := himg_card.symm
    _ ≤ (Finset.range (A.sum id + 1)).card := Finset.card_le_card himg_sub
    _ = A.sum id + 1 := Finset.card_range _

/- ## Part II: Structural Properties -/

/-- Subsets of sets with distinct subset sums also have distinct subset sums. -/
theorem hasDistinctSubsetSums_subset {A B : Finset ℕ}
    (hB : hasDistinctSubsetSums B) (hAB : A ⊆ B) :
    hasDistinctSubsetSums A := by
  intro S T hS hT heq
  exact hB S T (hS.trans hAB) (hT.trans hAB) heq

/-- Removing an element from a DSS set preserves DSS. -/
theorem hasDistinctSubsetSums_erase {A : Finset ℕ} {a : ℕ}
    (hA : hasDistinctSubsetSums A) :
    hasDistinctSubsetSums (A.erase a) :=
  hasDistinctSubsetSums_subset hA (Finset.erase_subset a A)

/- ## Part III: Small Case Verification -/

/-- The empty set trivially has distinct subset sums. -/
theorem dss_empty : hasDistinctSubsetSums (∅ : Finset ℕ) := by
  intro S T hS hT _
  rw [Finset.subset_empty] at hS hT
  rw [hS, hT]

/-- The singleton {1} has distinct subset sums: the two subsets ∅ and {1}
    have sums 0 and 1 respectively. This achieves f(1) = 1. -/
theorem dss_singleton_one : hasDistinctSubsetSums ({1} : Finset ℕ) := by
  intro S T hS hT heq
  rw [Finset.subset_singleton_iff] at hS hT
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;> simp_all

/- ## Part IV: Sum Bound Implies Counting Bound -/

/-- The sum bound recovers the element-wise counting bound as a corollary:
    since sum(A) ≤ n · max(A), we get 2^n ≤ n · N + 1. -/
theorem sum_bound_implies_counting {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.card * N + 1 := by
  have hsum := distinct_subset_sums_sum_bound hDistinct
  suffices A.sum id ≤ A.card * N by omega
  calc A.sum id
    ≤ A.sum (fun _ => N) :=
        Finset.sum_le_sum (fun a ha => hA a ha)
    _ = A.card * N := by rw [Finset.sum_const, smul_eq_mul]

/- ## Part V: The Conjecture and Known Bounds -/

/-- **Dubroff-Fox-Xu (2021)**: The best known lower bound.
    For A ⊆ {1,...,N} with n elements and DSS, N ≥ √(2/π) · 2^n / √n.

    This improves the simple counting bound N ≥ (2^n - 1)/n by
    removing the factor of n from the denominator (up to √n). -/
def dubroff_fox_xu_bound : Prop :=
  ∃ c : ℚ, c > 0 ∧ ∀ (A : Finset ℕ) (N : ℕ) (n : ℕ),
    n = A.card →
    n ≥ 1 →
    (∀ a ∈ A, a ≤ N) →
    (∀ a ∈ A, 0 < a) →
    hasDistinctSubsetSums A →
    (c * 2 ^ n : ℚ) ≤ N * Nat.sqrt n

/-- **Conway-Guy (1968)**: The conjectured extremal construction.
    There exist DSS sets with max element ≤ 0.22009 · 2^n.
    If optimal, then the constant c in Erdős's conjecture is c ≈ 0.22009. -/
def conway_guy_upper : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ (A : Finset ℕ) (N : ℕ),
    A.card = n ∧
    (∀ a ∈ A, a ≤ N) ∧
    (∀ a ∈ A, 0 < a) ∧
    hasDistinctSubsetSums A ∧
    (N : ℚ) ≤ (22009 : ℚ) / 100000 * 2 ^ n

/- ## Summary

**Theorems (6)**:
- distinct_subset_sums_sum_bound: 2^n ≤ sum(A) + 1
- hasDistinctSubsetSums_subset: DSS is hereditary
- hasDistinctSubsetSums_erase: erasing preserves DSS
- dss_empty: ∅ has DSS
- dss_singleton_one: {1} has DSS
- sum_bound_implies_counting: sum bound ⟹ counting bound

**Definitions (2)**:
- dubroff_fox_xu_bound: best known lower bound statement
- conway_guy_upper: upper bound construction statement

**Axioms (0)**, **Sorries (0)**
-/
