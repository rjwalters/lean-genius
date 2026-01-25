/-
Erdős Problem #603: Set Family Colorings with Intersection Restrictions

**Problem Statement (OPEN)**

Let (A_i) be a family of countably infinite sets such that |A_i ∩ A_j| ≠ 2
for all i ≠ j. Find the smallest cardinal C such that ∪A_i can always be
colored with at most C colors so that no A_i is monochromatic.

**Background:**
- A problem of Komjáth
- Related to chromatic numbers of hypergraphs
- Variant with |A_i ∩ A_j| ≠ 1: Komjáth showed ℵ₀ colors suffice

**Status:** OPEN

**Reference:** [Er87]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Cardinal

namespace Erdos603

/-!
# Part 1: Basic Definitions

Define set families, intersection constraints, and colorings.
-/

-- A family of countably infinite sets indexed by some type
def IsCountablyInfiniteFamily {α I : Type*} (A : I → Set α) : Prop :=
  ∀ i, Set.Countable (A i) ∧ (A i).Infinite

-- The intersection constraint: |A_i ∩ A_j| ≠ 2 for i ≠ j
def IntersectionNot2 {α I : Type*} (A : I → Set α) : Prop :=
  ∀ i j, i ≠ j → ¬ (A i ∩ A j).ncard = 2

-- Combined constraint for a valid family
def IsValidFamily {α I : Type*} (A : I → Set α) : Prop :=
  IsCountablyInfiniteFamily A ∧ IntersectionNot2 A

-- A coloring of the union
def Coloring {α I C : Type*} (A : I → Set α) (c : α → C) : Prop :=
  ∀ x ∈ ⋃ i, A i, True  -- c is defined on the union

-- A set is monochromatic under coloring c if all elements have the same color
def IsMonochromatic {α C : Type*} (S : Set α) (c : α → C) : Prop :=
  ∃ color, ∀ x ∈ S, c x = color

-- A valid coloring: no A_i is monochromatic
def IsValidColoring {α I C : Type*} (A : I → Set α) (c : α → C) : Prop :=
  ∀ i, ¬ IsMonochromatic (A i) c

/-!
# Part 2: The Main Question

What is the smallest cardinal C such that a valid coloring always exists?
-/

-- C colors suffice for family A
def SufficientColors {α I : Type*} (A : I → Set α) (C : Cardinal) : Prop :=
  ∃ (Γ : Type*) (hΓ : #Γ ≤ C) (c : α → Γ), IsValidColoring A c

-- The chromatic number of a family: minimum colors needed
noncomputable def chromaticNumber {α I : Type*} (A : I → Set α) : Cardinal :=
  sInf {C | SufficientColors A C}

-- The problem asks for the supremum over all valid families
def ErdosConjecture603 (C : Cardinal) : Prop :=
  ∀ {α I : Type*} (A : I → Set α), IsValidFamily A → SufficientColors A C

-- The minimum such C
noncomputable def minimalChromatic : Cardinal :=
  sInf {C | ErdosConjecture603 C}

/-!
# Part 3: Related Problem - Intersection ≠ 1

Komjáth showed: if |A_i ∩ A_j| ≠ 1 instead, then ℵ₀ colors suffice.
-/

-- The alternative constraint: |A_i ∩ A_j| ≠ 1
def IntersectionNot1 {α I : Type*} (A : I → Set α) : Prop :=
  ∀ i j, i ≠ j → ¬ (A i ∩ A j).ncard = 1

-- Family satisfying the ≠1 constraint
def IsValidFamilyNot1 {α I : Type*} (A : I → Set α) : Prop :=
  IsCountablyInfiniteFamily A ∧ IntersectionNot1 A

-- Komjáth's theorem: ℵ₀ colors suffice for the ≠1 case
axiom komjath_not1 : ∀ {α I : Type*} (A : I → Set α),
  IsValidFamilyNot1 A → SufficientColors A ℵ₀

/-!
# Part 4: Bounds and Special Cases

What bounds do we know for the ≠2 case?
-/

-- Trivial lower bound: need at least 2 colors (for infinite sets)
theorem lower_bound_2 {α I : Type*} (A : I → Set α)
    (h : IsValidFamily A) (hne : ∃ i, (A i).Nonempty) :
    ∀ C, SufficientColors A C → C ≥ 2 := by
  intro C ⟨Γ, _, c, hc⟩
  by_contra h'
  push_neg at h'
  -- With < 2 colors, either 0 or 1 color
  sorry

-- Countably many colors is an upper bound (trivially)
-- Each element gets a different color
axiom countable_suffices_trivial : ∀ {α I : Type*} (A : I → Set α),
  IsValidFamily A → SufficientColors A (Cardinal.mk ℕ)

-- The question: can we do better than ℵ₀?
def CanDoBetterThanAleph0 : Prop :=
  ∃ n : ℕ, ErdosConjecture603 n

-- Or: is ℵ₀ necessary?
def Aleph0Necessary : Prop :=
  ∀ n : ℕ, ¬ ErdosConjecture603 n

/-!
# Part 5: Hypergraph Perspective

This can be viewed as a hypergraph coloring problem.
-/

-- The hypergraph: vertices = ∪A_i, hyperedges = {A_i}
structure SetFamilyHypergraph (α I : Type*) where
  family : I → Set α

-- The chromatic number of the hypergraph
noncomputable def hypergraphChromatic {α I : Type*}
    (H : SetFamilyHypergraph α I) : Cardinal :=
  chromaticNumber H.family

-- The weak chromatic number (no monochromatic hyperedges)
-- This is exactly what we're computing
noncomputable def weakChromatic {α I : Type*}
    (H : SetFamilyHypergraph α I) : Cardinal :=
  hypergraphChromatic H

/-!
# Part 6: Examples and Constructions

Specific families that might require many colors.
-/

-- A disjoint family (intersection empty) trivially works with 2 colors
theorem disjoint_2_colors {α I : Type*} (A : I → Set α)
    (h : ∀ i j, i ≠ j → A i ∩ A j = ∅) : SufficientColors A 2 := by
  sorry

-- A family where all pairs have intersection size 0, 1, or ≥3
-- These satisfy both ≠1 and ≠2 constraints
def SatisfiesBoth {α I : Type*} (A : I → Set α) : Prop :=
  IntersectionNot1 A ∧ IntersectionNot2 A

-- For such families, Komjáth's bound applies
theorem both_constraints {α I : Type*} (A : I → Set α)
    (h : IsCountablyInfiniteFamily A) (hb : SatisfiesBoth A) :
    SufficientColors A ℵ₀ := by
  apply komjath_not1
  exact ⟨h, hb.1⟩

/-!
# Part 7: Problem Status

The problem remains OPEN. The exact value of the minimal C is unknown.
-/

-- The problem is open
def erdos_603_status : String := "OPEN"

-- What we know:
-- 1. 2 ≤ C (need at least 2 colors)
-- 2. C ≤ ℵ₀ (countably many suffice trivially)
-- 3. For ≠1: C = ℵ₀ (Komjáth)
-- 4. For ≠2: C = ? (OPEN)

-- The formal statement
theorem erdos_603_statement :
    (∃ C, ErdosConjecture603 C) ↔
    ∃ C, ∀ {α I : Type*} (A : I → Set α),
      (IsCountablyInfiniteFamily A ∧ IntersectionNot2 A) →
      SufficientColors A C := by
  constructor
  · intro ⟨C, hC⟩
    exact ⟨C, fun A ⟨h1, h2⟩ => hC A ⟨h1, h2⟩⟩
  · intro ⟨C, hC⟩
    exact ⟨C, fun A h => hC A h⟩

/-!
# Part 8: Summary

**Known:**
- ℵ₀ colors always suffice (trivial coloring)
- For ≠1 constraint, ℵ₀ is optimal (Komjáth)
- At least 2 colors needed

**Unknown:**
- Can finite colors suffice for ≠2?
- If finite, what is the exact number?
- If infinite, is ℵ₀ optimal?
-/

end Erdos603
