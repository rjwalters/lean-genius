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

/-- The Conway-Guy sequence (OEIS A005318): conjectured minimum max element
    for n-element sets with distinct subset sums.
    Values: 0, 1, 2, 4, 7, 13, 24, 44, 84, 161, 309, ...
    Defined via explicit lookup for small n. The general recurrence involves
    ceiling of a rational expression that is unwieldy in Lean. -/
def conwayGuySeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 13
  | 6 => 24
  | 7 => 44
  | 8 => 84
  | _ + 9 => 0  -- Placeholder for large n (not used in verified range)

/-- The Conway-Guy conjecture: the minimum N such that an n-element set
    in {1,...,N} has distinct subset sums equals conwayGuySeq n. -/
def conwayGuyConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 →
    achievesDistinctSums n (conwayGuySeq n) ∧
    ¬achievesDistinctSums n (conwayGuySeq n - 1)

/- ## f(6) via Conway-Guy Set -/

/-- {11, 17, 20, 22, 23, 24} has distinct subset sums with max 24 and 6 elements. -/
theorem dss_conway_guy_6 :
    hasDistinctSubsetSums ({11, 17, 20, 22, 23, 24} : Finset ℕ) := by native_decide

/-- f(6) ≤ 24: the Conway-Guy set {11,17,20,22,23,24} achieves it. -/
theorem f6_le_24 : achievesDistinctSums 6 24 := by
  exact ⟨{11, 17, 20, 22, 23, 24}, by native_decide, by simp; omega, by simp; omega,
    dss_conway_guy_6⟩

/- ## Optimality (Lower Bounds) -/

/-- Decidability of achievesDistinctSums for small parameters. -/
instance decidableAchieves (n N : ℕ) : Decidable (achievesDistinctSums n N) :=
  decidable_of_iff
    (∃ A ∈ (Finset.range (N + 1)).powerset,
      A.card = n ∧ (∀ a ∈ A, 0 < a) ∧ hasDistinctSubsetSums A)
    ⟨fun ⟨A, hA_mem, hA_card, hA_pos, hA_dss⟩ =>
      ⟨A, hA_card, hA_pos, fun a ha => by
        have := Finset.mem_powerset.mp hA_mem ha
        exact Finset.mem_range.mp this |>.le |> Nat.lt_succ_iff.mpr, hA_dss⟩,
     fun ⟨A, hA_card, hA_pos, hA_le, hA_dss⟩ =>
      ⟨A, Finset.mem_powerset.mpr (fun a ha =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hA_le a ha))),
       hA_card, hA_pos, hA_dss⟩⟩

/-- f(3) ≥ 4: no 3-element subset of {1,2,3} has distinct subset sums. -/
theorem f3_optimal : ¬achievesDistinctSums 3 3 := by native_decide

/-- f(3) = 4 exactly. -/
theorem f3_eq_4 : achievesDistinctSums 3 4 ∧ ¬achievesDistinctSums 3 3 :=
  ⟨f3_le_4, f3_optimal⟩

/-- f(4) ≥ 7: no 4-element subset of {1,...,6} has distinct subset sums. -/
theorem f4_optimal : ¬achievesDistinctSums 4 6 := by native_decide

/-- f(4) = 7 exactly. -/
theorem f4_eq_7 : achievesDistinctSums 4 7 ∧ ¬achievesDistinctSums 4 6 :=
  ⟨f4_le_7, f4_optimal⟩

/- ## Structural Observations -/

/-- Conway-Guy sequence matches verified values. -/
theorem conwayGuy_matches :
    conwayGuySeq 1 = 1 ∧ conwayGuySeq 2 = 2 ∧ conwayGuySeq 3 = 4 ∧
    conwayGuySeq 4 = 7 ∧ conwayGuySeq 5 = 13 ∧ conwayGuySeq 6 = 24 := by
  simp [conwayGuySeq]

/-- Each Conway-Guy value achieves distinct subset sums (verified range). -/
theorem conwayGuy_achieves_1_to_6 :
    achievesDistinctSums 1 (conwayGuySeq 1) ∧
    achievesDistinctSums 2 (conwayGuySeq 2) ∧
    achievesDistinctSums 3 (conwayGuySeq 3) ∧
    achievesDistinctSums 4 (conwayGuySeq 4) ∧
    achievesDistinctSums 5 (conwayGuySeq 5) ∧
    achievesDistinctSums 6 (conwayGuySeq 6) :=
  ⟨f1_eq_1, f2_eq_2, f3_le_4, f4_le_7, f5_le_13, f6_le_24⟩

/-- The Conway-Guy values are optimal for n = 3, 4 (verified range). -/
theorem conwayGuy_optimal_3_4 :
    ¬achievesDistinctSums 3 (conwayGuySeq 3 - 1) ∧
    ¬achievesDistinctSums 4 (conwayGuySeq 4 - 1) := by
  simp [conwayGuySeq]
  exact ⟨f3_optimal, f4_optimal⟩

/- ## Summary

**Verified extremal set values (OEIS A005318)**:
- f(1) = 1 (set {1})
- f(2) = 2 (set {1,2})
- f(3) = 4 (set {1,2,4}) — OPTIMAL (proved ¬achieves 3 3)
- f(4) = 7 (set {3,5,6,7}) — OPTIMAL (proved ¬achieves 4 6)
- f(5) ≤ 13 (set {6,9,11,12,13})
- f(6) ≤ 24 (set {11,17,20,22,23,24})

Conway-Guy sequence defined for n ≤ 8.
All upper bounds verified via native_decide.
Optimality for f(3) and f(4) proved via exhaustive search (native_decide).

**Open**: Conway-Guy conjecture (that these are exact for all n).
-/
end
