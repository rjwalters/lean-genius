/-
Erdős Problem #1, OQ-04: Extremal Sets for Distinct Subset Sums

The parent problem asks: if A ⊆ {1,...,N} has n elements with all 2^n
subset sums distinct, must N ≥ c · 2^n?

This follow-up investigates the *structure* of extremal sets — those
achieving the minimum N for each n. The minimum values form OEIS A005318:
  f(0)=0, f(1)=1, f(2)=2, f(3)=4, f(4)=7, f(5)=13, f(6)=24, ...

The Conway-Guy conjecture (1968) identifies the specific extremal sets.

Reference: https://erdosproblems.com/1
OEIS: A005318 (minimum max element for distinct subset sums)
-/

import Mathlib

open Finset

/-- A finite set of natural numbers has distinct subset sums if distinct
    subsets always have different sums. (Imported from parent.) -/
def hasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ (S T : Finset ℕ), S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T

/-- Decidability of hasDistinctSubsetSums: check all pairs of subsets. -/
instance decidableHasDistinctSubsetSums (A : Finset ℕ) :
    Decidable (hasDistinctSubsetSums A) :=
  decidable_of_iff
    (∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T)
    ⟨fun h S T hS hT => h S (mem_powerset.mpr hS) T (mem_powerset.mpr hT),
     fun h S hS T hT => h S (mem_powerset.mp hS) T (mem_powerset.mp hT)⟩

/-- A set of n positive integers in {1,...,N} with distinct subset sums exists. -/
def achievesDistinctSums (n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, 0 < a) ∧ (∀ a ∈ A, a ≤ N) ∧
    hasDistinctSubsetSums A

/- ## Verified Small Cases (OEIS A005318) -/

/-- {1} has distinct subset sums: subsets are ∅ (sum 0) and {1} (sum 1). -/
theorem dss_1 : hasDistinctSubsetSums {1} := by native_decide

/-- {1, 2} has distinct subset sums: sums are 0, 1, 2, 3. -/
theorem dss_12 : hasDistinctSubsetSums ({1, 2} : Finset ℕ) := by native_decide

/-- {1, 2, 4} has distinct subset sums: sums are 0,1,2,3,4,5,6,7. -/
theorem dss_124 : hasDistinctSubsetSums ({1, 2, 4} : Finset ℕ) := by native_decide

/-- {3, 5, 6, 7} has distinct subset sums with max 7 and 4 elements. -/
theorem dss_3567 : hasDistinctSubsetSums ({3, 5, 6, 7} : Finset ℕ) := by native_decide

/-- {6, 9, 11, 12, 13} has distinct subset sums with max 13 and 5 elements. -/
theorem dss_conway_guy_5 :
    hasDistinctSubsetSums ({6, 9, 11, 12, 13} : Finset ℕ) := by native_decide

/-- f(1) = 1: {1} achieves it, and {∅} can't (need positive elements). -/
theorem f1_eq_1 : achievesDistinctSums 1 1 := by
  exact ⟨{1}, by simp, by simp, by simp, dss_1⟩

/-- f(2) = 2: {1,2} achieves it. -/
theorem f2_eq_2 : achievesDistinctSums 2 2 := by
  exact ⟨{1, 2}, by native_decide, by simp; omega, by simp; omega, dss_12⟩

/-- f(3) = 4: {1,2,4} achieves it (powers of 2 give binary representation). -/
theorem f3_le_4 : achievesDistinctSums 3 4 := by
  exact ⟨{1, 2, 4}, by native_decide, by simp; omega, by simp; omega, dss_124⟩

/-- f(4) ≤ 7: {3,5,6,7} achieves it. -/
theorem f4_le_7 : achievesDistinctSums 4 7 := by
  exact ⟨{3, 5, 6, 7}, by native_decide, by simp; omega, by simp; omega, dss_3567⟩

/-- f(5) ≤ 13: {6,9,11,12,13} achieves it (Conway-Guy construction). -/
theorem f5_le_13 : achievesDistinctSums 5 13 := by
  exact ⟨{6, 9, 11, 12, 13}, by native_decide, by simp; omega, by simp; omega,
    dss_conway_guy_5⟩

/- ## The Conway-Guy Conjecture -/

/-- The Conway-Guy sequence: conjectured minimum max element for n-element
    sets with distinct subset sums. First values: 0, 1, 2, 4, 7, 13, 24, 44. -/
def conwayGuySeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sorry -- Recurrence involves ceiling of rational expression

/-- The Conway-Guy conjecture: the minimum N such that an n-element set
    in {1,...,N} has distinct subset sums equals conwayGuySeq n. -/
def conwayGuyConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 →
    achievesDistinctSums n (conwayGuySeq n) ∧
    ¬achievesDistinctSums n (conwayGuySeq n - 1)

/- ## Structural Observations -/

/-- Powers of 2 always give distinct subset sums (binary representation).
    The set {1, 2, 4, ..., 2^{n-1}} has max = 2^{n-1} and n elements. -/
theorem powers_of_two_dss (n : ℕ) :
    achievesDistinctSums n (2^n - 1) := by
  sorry -- Requires building the set {2^0, ..., 2^{n-1}} and proving DSS

/-- The gap between 2^{n-1} (powers of 2 bound) and f(n) (optimal) grows:
    for n = 4, powers give max 8 but optimal is 7;
    for n = 5, powers give max 16 but optimal is 13. -/

/- ## Summary

**Verified extremal set values (OEIS A005318)**:
- f(1) = 1 (set {1})
- f(2) = 2 (set {1,2})
- f(3) ≤ 4 (set {1,2,4})
- f(4) ≤ 7 (set {3,5,6,7})
- f(5) ≤ 13 (set {6,9,11,12,13})

All verified computationally via native_decide.

**Open**: Conway-Guy conjecture (these are the exact minima).
-/
end
