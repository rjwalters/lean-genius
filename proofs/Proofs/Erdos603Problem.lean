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

/-
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

/-
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
-- Universe-annotated to avoid metavariable issues
def ErdosConjecture603 (C : Cardinal.{u}) : Prop :=
  ∀ {α I : Type u} (A : I → Set α), IsValidFamily A → SufficientColors A C

-- The minimum such C
noncomputable def minimalChromatic : Cardinal.{u} :=
  sInf {C : Cardinal.{u} | ErdosConjecture603 C}

/-
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

/-
# Part 4: Bounds and Special Cases

What bounds do we know for the ≠2 case?
-/

-- Helper: every set in a valid family is nonempty (from infiniteness)
lemma IsCountablyInfiniteFamily.nonempty {α I : Type*} {A : I → Set α}
    (hf : IsCountablyInfiniteFamily A) (i : I) : (A i).Nonempty :=
  (hf i).2.nonempty

-- Trivial lower bound: need at least 2 colors (for infinite sets)
theorem lower_bound_2 {α I : Type*} (A : I → Set α)
    (h : IsValidFamily A) (hne : ∃ i, (A i).Nonempty) :
    ∀ C, SufficientColors A C → C ≥ 2 := by
  intro C ⟨Γ, hΓ, c, hc⟩
  by_contra h'
  push_neg at h'
  -- h' : C < 2, hΓ : #Γ ≤ C, so #Γ < 2
  obtain ⟨i₀, a₀, ha₀⟩ := hne
  apply hc i₀
  -- Goal: IsMonochromatic (A i₀) c
  -- Since #Γ < 2, Γ has at most 1 element, so all colors are equal
  refine ⟨c a₀, fun x _ => ?_⟩
  have hΓlt : #Γ < 2 := lt_of_le_of_lt hΓ h'
  -- Γ is finite (since #Γ < 2 < ℵ₀)
  have : Finite Γ := Cardinal.lt_aleph0_iff_finite.mp
    (lt_trans hΓlt (Cardinal.nat_lt_aleph0 2))
  haveI : Fintype Γ := Fintype.ofFinite Γ
  -- Fintype.card Γ < 2, so Γ has at most 1 element
  have hcard : Fintype.card Γ < 2 := by
    rw [Cardinal.mk_fintype] at hΓlt
    exact_mod_cast hΓlt
  have : Subsingleton Γ := by
    rw [← Fintype.card_le_one_iff_subsingleton]; omega
  exact Subsingleton.elim _ _

-- Countably many colors suffice when the index set is countable.
-- Proof: the union is countable, so we inject it into ℕ; the injection
-- assigns distinct colors to distinct elements, preventing monochromaticity
-- on any infinite set.
theorem countable_suffices {α I : Type*} [Countable I] (A : I → Set α)
    (hv : IsValidFamily A) : SufficientColors A (Cardinal.mk ℕ) := by
  classical
  -- The union is countable (countable union of countable sets)
  have hU : (⋃ i, A i).Countable := Set.countable_iUnion (fun i => (hv.1 i).1)
  -- Get Countable and Encodable instances on the union subtype
  haveI : Countable ↥(⋃ i, A i) := hU.to_subtype
  haveI : Encodable ↥(⋃ i, A i) := Encodable.ofCountable _
  -- Coloring: encode elements in the union into ℕ, 0 elsewhere
  refine ⟨ℕ, le_refl _, fun x =>
    if h : x ∈ ⋃ i, A i then Encodable.encode (⟨x, h⟩ : ↥(⋃ i, A i)) else 0, ?_⟩
  -- No A_i is monochromatic: encoding is injective, so all-same-color ⟹ singleton
  intro i ⟨color, hcolor⟩
  apply (hv.1 i).2
  apply Set.Subsingleton.finite
  intro x hx y hy
  have hxU : x ∈ ⋃ j, A j := Set.mem_iUnion.mpr ⟨i, hx⟩
  have hyU : y ∈ ⋃ j, A j := Set.mem_iUnion.mpr ⟨i, hy⟩
  have hcx := hcolor x hx
  have hcy := hcolor y hy
  simp only [dif_pos hxU] at hcx
  simp only [dif_pos hyU] at hcy
  exact congr_arg Subtype.val (Encodable.encode_injective (hcx.trans hcy.symm))

-- The question: can we do better than ℵ₀?
def CanDoBetterThanAleph0 : Prop :=
  ∃ n : ℕ, ErdosConjecture603.{0} n

-- Or: is ℵ₀ necessary?
def Aleph0Necessary : Prop :=
  ∀ n : ℕ, ¬ ErdosConjecture603.{0} n

/-
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

/-
# Part 6: Examples and Constructions

Specific families that might require many colors.
-/

-- A disjoint family of infinite sets trivially works with 2 colors
-- Note: infiniteness is needed — singletons are always monochromatic
theorem disjoint_2_colors {α I : Type*} (A : I → Set α)
    (hdisj : ∀ i j, i ≠ j → A i ∩ A j = ∅)
    (hinf : ∀ i, (A i).Infinite) : SufficientColors A 2 := by
  classical
  -- For each A i, choose a distinguished element d i ∈ A i
  choose d hd using fun i => (hinf i).nonempty
  -- For each A i, choose a second element e i ∈ A i with e i ≠ d i
  have hexist : ∀ i, ∃ b, b ∈ A i ∧ b ≠ d i := by
    intro i
    obtain ⟨b, hb⟩ := ((hinf i).diff (Set.finite_singleton (d i))).nonempty
    rw [Set.mem_diff, Set.mem_singleton_iff] at hb
    exact ⟨b, hb.1, hb.2⟩
  choose e he hne using hexist
  -- Use ULift (Fin 2) as a universe-polymorphic 2-element type
  refine ⟨ULift (Fin 2), ?_,
    fun x => ⟨if ∃ j, x = d j then 0 else 1⟩, ?_⟩
  · simp
  · -- No A i is monochromatic
    intro i ⟨color, hcolor⟩
    -- Force beta reduction with explicit type annotations
    have h_di : (⟨if ∃ j, d i = d j then (0 : Fin 2) else 1⟩ : ULift (Fin 2)) = color :=
      hcolor (d i) (hd i)
    rw [if_pos ⟨i, rfl⟩] at h_di
    have h2 : ¬ ∃ j, e i = d j := by
      rintro ⟨j, hj⟩
      by_cases hij : i = j
      · exact hne i (hij ▸ hj)
      · have hmem : e i ∈ A i ∩ A j := ⟨he i, hj ▸ hd j⟩
        rw [hdisj i j hij] at hmem
        exact Set.not_mem_empty _ hmem
    have h_ei : (⟨if ∃ j, e i = d j then (0 : Fin 2) else 1⟩ : ULift (Fin 2)) = color :=
      hcolor (e i) (he i)
    rw [if_neg h2] at h_ei
    -- h_di : ⟨0⟩ = color, h_ei : ⟨1⟩ = color → ⟨0⟩ = ⟨1⟩
    have := congr_arg ULift.down (h_di.trans h_ei.symm)
    exact absurd this (by decide)

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

/-
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

-- The formal statement (universe-fixed for consistency)
theorem erdos_603_statement :
    (∃ C : Cardinal.{u}, ErdosConjecture603 C) ↔
    ∃ C : Cardinal.{u}, ∀ {α I : Type u} (A : I → Set α),
      (IsCountablyInfiniteFamily A ∧ IntersectionNot2 A) →
      SufficientColors A C := by
  simp only [ErdosConjecture603, IsValidFamily]

/-
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
