/-
Erdős Problem #1027: Intersecting Sets and Property B

Let c > 0 and n sufficiently large. Suppose F is a family of at most c·2^n sets,
each of size n. Let X = ∪F. Must there exist ≫_c 2^|X| sets B ⊆ X that intersect
every set in F, yet contain none of them?

**Status**: SOLVED (YES)
**Answer**: Such sets exist in abundance (proved by Koishi Chan)

Reference: https://erdosproblems.com/1027
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

open Finset

namespace Erdos1027

/-
## Set Families

We work with families of n-element sets.
-/

variable {α : Type*} [DecidableEq α]

/-- A set family is a collection of sets. -/
abbrev SetFamily (α : Type*) [DecidableEq α] := Finset (Finset α)

/-- The union of all sets in a family. -/
def familyUnion (F : SetFamily α) : Finset α :=
  F.sup id

/-- A family is n-uniform if all sets have size n. -/
def isNUniform (F : SetFamily α) (n : ℕ) : Prop :=
  ∀ A ∈ F, A.card = n

/-
## Intersecting and Non-Containing Sets

A set B intersects A if their intersection is nonempty.
A set B contains A if A ⊆ B.
-/

/-- B intersects every set in F. -/
def intersectsAll (B : Finset α) (F : SetFamily α) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty

/-- B contains no set in F. -/
def containsNone (B : Finset α) (F : SetFamily α) : Prop :=
  ∀ A ∈ F, ¬(A ⊆ B)

/-- B is a "good" set: intersects all but contains none. -/
def isGoodSet (B : Finset α) (F : SetFamily α) : Prop :=
  intersectsAll B F ∧ containsNone B F

/-- The collection of all good sets. -/
def goodSets (F : SetFamily α) : Set (Finset α) :=
  { B | isGoodSet B F ∧ B ⊆ familyUnion F }

/-
## Property B (2-Chromatic)

A family has Property B if there exists a 2-coloring such that
no set is monochromatic. Equivalently, there exists a set B that
intersects every set but contains none.
-/

/-- F has Property B if there exists a good set. -/
def hasPropertyB (F : SetFamily α) : Prop :=
  ∃ B : Finset α, isGoodSet B F

/-- Property B is equivalent to 2-colorability. -/
def is2Colorable (F : SetFamily α) : Prop :=
  ∃ f : α → Bool, ∀ A ∈ F, (∃ x ∈ A, f x = true) ∧ (∃ y ∈ A, f y = false)

/-- Property B ↔ 2-colorable. -/
theorem propertyB_iff_2colorable (F : SetFamily α) :
    hasPropertyB F ↔ is2Colorable F := by
  sorry

/-
## The Main Question

For families of bounded size, are there many good sets?
-/

/-- Count of good sets (as a natural number). -/
noncomputable def goodSetCount (F : SetFamily α) [Fintype α] : ℕ :=
  (Finset.univ.powerset.filter (fun B => isGoodSet B F ∧ B ⊆ familyUnion F)).card

/-- The main conjecture: many good sets exist. -/
def erdos_1027_conjecture (c : ℝ) : Prop :=
  c > 0 → ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : SetFamily α,
      isNUniform F n →
      (F.card : ℝ) ≤ c * 2^n →
      (goodSetCount F : ℝ) ≥ δ * 2^(familyUnion F).card

/-
## The Solution

The conjecture is true (proved by Koishi Chan).
-/

/-- The main theorem: many good sets exist for bounded families. -/
axiom erdos_1027_solution : ∀ c > 0, erdos_1027_conjecture c

/-- Simplified statement of the result. -/
theorem erdos_1027_solved (c : ℝ) (hc : c > 0) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : SetFamily α,
      isNUniform F n →
      (F.card : ℝ) ≤ c * 2^n →
      (goodSetCount F : ℝ) ≥ δ * 2^(familyUnion F).card := by
  exact erdos_1027_solution c hc

/-
## Connection to Problem 901

Problem 901 establishes that Property B is equivalent to 2-colorability.
-/

/-- Reference to Problem 901. -/
def problem_901_connection : Prop :=
  ∀ (α : Type*) [DecidableEq α], ∀ F : SetFamily α,
    hasPropertyB F ↔ is2Colorable F

/-- The connection holds. -/
theorem problem_901 : problem_901_connection := by
  intro α _ F
  exact propertyB_iff_2colorable F

/-
## Existence of a Single Good Set

Before counting, we need existence.
-/

/-- For n-uniform families of size ≤ c·2^n, Property B holds. -/
axiom propertyB_for_bounded (c : ℝ) (hc : c > 0) :
  ∃ N : ℕ, ∀ n ≥ N,
    ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : SetFamily α,
      isNUniform F n →
      (F.card : ℝ) ≤ c * 2^n →
      hasPropertyB F

/-- Single good set implies many good sets (the key insight). -/
theorem single_implies_many (F : SetFamily α) [Fintype α]
    (hB : hasPropertyB F) :
    ∃ δ > 0, (goodSetCount F : ℝ) ≥ δ * 2^(familyUnion F).card := by
  sorry

/-
## Probabilistic Intuition

Random sets often satisfy both conditions.
-/

/-- Probability a random set intersects A (of size n). -/
noncomputable def probIntersects (n : ℕ) : ℝ :=
  1 - (1/2)^n

/-- Probability a random set doesn't contain A (of size n). -/
noncomputable def probNotContains (n : ℕ) : ℝ :=
  1 - (1/2)^n

/-- Expected number of good sets (heuristic). -/
noncomputable def expectedGoodSets (F : SetFamily α) [Fintype α] (n : ℕ) : ℝ :=
  2^(familyUnion F).card * (probIntersects n)^F.card * (probNotContains n)^F.card

/-- For bounded F, expected good sets is large. -/
theorem expected_good_positive (c : ℝ) (hc : c > 0) :
    ∃ N : ℕ, ∀ n ≥ N,
    ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : SetFamily α,
      isNUniform F n →
      (F.card : ℝ) ≤ c * 2^n →
      expectedGoodSets F n > 0 := by
  sorry

/-
## Density of Good Sets

The fraction of subsets that are good is bounded below.
-/

/-- Density of good sets among all subsets of X. -/
noncomputable def goodSetDensity (F : SetFamily α) [Fintype α] : ℝ :=
  (goodSetCount F : ℝ) / 2^(familyUnion F).card

/-- The density is bounded below for bounded families. -/
axiom goodSetDensity_lower (c : ℝ) (hc : c > 0) :
  ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : SetFamily α,
      isNUniform F n →
      (F.card : ℝ) ≤ c * 2^n →
      goodSetDensity F ≥ δ

/-
## Special Cases

Small families have many good sets.
-/

/-- Empty family: all non-empty sets are good. -/
theorem empty_family_good [Fintype α] :
    goodSetCount (∅ : SetFamily α) = 2^Fintype.card α := by
  sorry

/-- Singleton family {A}: good sets are those intersecting A but not containing A. -/
theorem singleton_family_good (A : Finset α) [Fintype α] (hA : A.Nonempty) :
    goodSetCount ({A} : SetFamily α) ≥ 2^(A.card - 1) := by
  sorry

/-
## The Counting Argument

Key lemma for the proof.
-/

/-- Inclusion-exclusion for good sets. -/
theorem good_set_inclusion_exclusion (F : SetFamily α) [Fintype α] :
    ∃ (lower : ℕ), goodSetCount F ≥ lower ∧
      (lower : ℝ) ≥ (1/4) * 2^(familyUnion F).card - F.card * 2^((familyUnion F).card - 1) := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1027 on intersecting set families.

**Status**: SOLVED

**The Question**: For families F of ≤ c·2^n sets of size n, must there
exist ≫_c 2^|X| sets B that intersect all members but contain none?

**The Answer**: YES (proved by Koishi Chan).

**Key Results**:
- Property B (2-chromatic) ↔ single good set exists
- Bounded families have Property B for large n
- Many good sets exist (positive density)

**Related Topics**:
- Property B and 2-colorability
- Probabilistic method
- Problem 901 connection
-/

end Erdos1027
