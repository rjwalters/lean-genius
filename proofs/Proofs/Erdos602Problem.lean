/-
Erdős Problem #602: 2-Coloring of Set Families with Property B

**Problem Statement (OPEN)**

Let (A_i) be a family of sets where |A_i| = ℵ₀ for all i. For any i ≠ j,
the intersection |A_i ∩ A_j| is finite and not equal to 1.

Is there a 2-coloring of ∪A_i such that no A_i is monochromatic?

**Context:**
- This is "Property B" for infinite families
- Attributed to Komjáth
- Conditions prevent trivial cases and certain structural patterns

**Status:** OPEN

**Reference:** [Er87]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Cardinal

namespace Erdos602

/-!
# Part 1: Basic Definitions

Define set families and their properties.
-/

-- A family of sets indexed by some type I
-- Each set A_i is a subset of some universe U

-- The universe of elements
variable {U : Type*}

-- Index type for the family
variable {I : Type*}

-- A family of sets
abbrev SetFamily (U I : Type*) := I → Set U

-- A set is countably infinite
def IsCountablyInfinite (S : Set U) : Prop :=
  Cardinal.mk S = Cardinal.aleph0

-- All sets in the family are countably infinite
def AllCountablyInfinite (A : SetFamily U I) : Prop :=
  ∀ i, IsCountablyInfinite (A i)

/-!
# Part 2: Intersection Conditions

The pairwise intersections must be finite but not exactly 1.
-/

-- Intersection is finite
def HasFiniteIntersection (A : SetFamily U I) (i j : I) : Prop :=
  (A i ∩ A j).Finite

-- Intersection has cardinality ≠ 1
def IntersectionNotOne (A : SetFamily U I) (i j : I) : Prop :=
  Cardinal.mk (A i ∩ A j) ≠ 1

-- Combined condition for distinct pairs
def ValidIntersection (A : SetFamily U I) (i j : I) : Prop :=
  HasFiniteIntersection A i j ∧ IntersectionNotOne A i j

-- The family satisfies the intersection property
def HasValidIntersections (A : SetFamily U I) : Prop :=
  ∀ i j, i ≠ j → ValidIntersection A i j

-- A valid Erdős family
def IsErdosFamily (A : SetFamily U I) : Prop :=
  AllCountablyInfinite A ∧ HasValidIntersections A

/-!
# Part 3: 2-Colorings

A coloring assigns each element to one of two colors.
-/

-- A 2-coloring is a function to Bool
abbrev TwoColoring (U : Type*) := U → Bool

-- The elements of color c in set S
def ColoredSubset (c : Bool) (coloring : TwoColoring U) (S : Set U) : Set U :=
  S ∩ {x | coloring x = c}

-- A set is monochromatic under a coloring
def IsMonochromatic (S : Set U) (coloring : TwoColoring U) : Prop :=
  (∀ x ∈ S, coloring x = true) ∨ (∀ x ∈ S, coloring x = false)

-- Equivalently: one color class is empty in S
def IsMonochromaticAlt (S : Set U) (coloring : TwoColoring U) : Prop :=
  ColoredSubset true coloring S = ∅ ∨ ColoredSubset false coloring S = ∅

-- A set has Property B if it admits a non-monochromatic coloring
def HasPropertyB (S : Set U) : Prop :=
  ∃ coloring : TwoColoring U, ¬IsMonochromatic S coloring

/-!
# Part 4: Property B for Families

A family has Property B if there's a coloring where no member is monochromatic.
-/

-- A coloring works for the family
def IsValidColoring (A : SetFamily U I) (coloring : TwoColoring U) : Prop :=
  ∀ i, ¬IsMonochromatic (A i) coloring

-- The family has Property B
def FamilyHasPropertyB (A : SetFamily U I) : Prop :=
  ∃ coloring : TwoColoring U, IsValidColoring A coloring

-- Erdős's question: does every Erdős family have Property B?
def ErdosQuestion602 : Prop :=
  ∀ (U : Type*) (I : Type*) (A : SetFamily U I),
    IsErdosFamily A → FamilyHasPropertyB A

/-!
# Part 5: The Main Conjecture

Formal statement of Erdős Problem #602.
-/

-- The main conjecture
def ErdosConjecture602 : Prop := ErdosQuestion602

-- Equivalently: no Erdős family is a counterexample
def NoCounterexample : Prop :=
  ¬∃ (U : Type*) (I : Type*) (A : SetFamily U I),
    IsErdosFamily A ∧ ¬FamilyHasPropertyB A

-- These should be equivalent
theorem conjecture_equiv : ErdosConjecture602 ↔ NoCounterexample := by
  constructor
  · intro h ⟨U, I, A, hA, hnB⟩
    exact hnB (h U I A hA)
  · intro h U I A hA
    by_contra hnB
    exact h ⟨U, I, A, hA, hnB⟩

/-!
# Part 6: Why the Conditions Matter

Explain the role of each condition.
-/

-- Condition: |A_i| = ℵ₀
-- Without this: finite sets trivially have Property B (pigeonhole for size > 2)

-- Condition: |A_i ∩ A_j| < ℵ₀
-- Without this: if intersections are infinite, can force monochromatic

-- Condition: |A_i ∩ A_j| ≠ 1
-- This is crucial and non-obvious. Why exclude exactly 1?
-- With single-element intersections, one can construct counterexamples

-- Example of why |A ∩ B| = 1 is problematic (informal):
-- If many pairs share exactly one element, that element's color
-- forces constraints that can't all be satisfied

/-!
# Part 7: Related Property B Results

Classical results about Property B.
-/

-- Miller's theorem: finite set systems with |A_i| ≥ 2 have Property B
-- (Not directly applicable here since sets are infinite)

-- For finite hypergraphs, Property B is well-studied
-- The infinite case with the specific intersection conditions is harder

-- Komjáth originally posed this problem
def KomjathProblem : Prop := ErdosQuestion602

/-!
# Part 8: Special Cases

Analyze special cases of the family structure.
-/

-- If I is countable
def CountableIndex (I : Type*) : Prop := Cardinal.mk I ≤ Cardinal.aleph0

-- Disjoint families trivially have Property B
def IsDisjointFamily (A : SetFamily U I) : Prop :=
  ∀ i j, i ≠ j → A i ∩ A j = ∅

theorem disjoint_has_property_b {A : SetFamily U I} (hA : IsDisjointFamily A) :
    FamilyHasPropertyB A := by
  -- For disjoint family, color each set with both colors
  sorry -- Requires constructing explicit coloring

-- Almost disjoint families (finite intersections) are the interesting case
def IsAlmostDisjoint (A : SetFamily U I) : Prop :=
  ∀ i j, i ≠ j → (A i ∩ A j).Finite

/-!
# Part 9: Obstructions to Property B

What would make a family fail to have Property B?
-/

-- If the family is 2-chromatic-forcing
-- (No coloring avoids a monochromatic member)
def Is2ChromaticForcing (A : SetFamily U I) : Prop :=
  ∀ coloring : TwoColoring U, ∃ i, IsMonochromatic (A i) coloring

-- Counterexample would require this
theorem counterexample_structure :
    (∃ (U : Type*) (I : Type*) (A : SetFamily U I),
      IsErdosFamily A ∧ Is2ChromaticForcing A) ↔ ¬ErdosConjecture602 := by
  constructor
  · intro ⟨U, I, A, hE, hF⟩ h602
    have hB := h602 U I A hE
    obtain ⟨c, hc⟩ := hB
    obtain ⟨i, hi⟩ := hF c
    exact hc i hi
  · intro h
    push_neg at h
    simp only [ErdosConjecture602, ErdosQuestion602, FamilyHasPropertyB,
               IsValidColoring] at h
    obtain ⟨U, I, A, hE, hA⟩ := h
    refine ⟨U, I, A, hE, ?_⟩
    intro c
    push_neg at hA
    exact hA c

/-!
# Part 10: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_602_status : String := "OPEN"

-- Main formal statement
theorem erdos_602_statement :
    ErdosConjecture602 ↔
    ∀ (U : Type*) (I : Type*) (A : SetFamily U I),
      IsErdosFamily A → FamilyHasPropertyB A := by
  rfl

/-!
# Summary

**Problem:** Given a family of countably infinite sets with pairwise intersections
that are finite but not exactly 1, does there exist a 2-coloring of the union
such that no member set is monochromatic?

**Known:**
- Komjáth posed this problem
- Property B is well-studied for finite hypergraphs
- The intersection ≠ 1 condition is crucial

**Unknown:**
- Whether every such family has Property B
- Structure of potential counterexamples

**Difficulty:** Combines infinite set theory with combinatorial coloring.
-/

end Erdos602
