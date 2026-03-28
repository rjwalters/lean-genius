/-
  Erdős Problem #1027: Intersecting Sets and Property B

  Let c > 0 and n be sufficiently large. Suppose F is a family of at most
  c · 2^n sets, each of size n. Let X = ∪F.

  Must there exist ≫_c 2^|X| sets B ⊆ X which intersect every set in F,
  yet contain none of them?

  **Answer**: YES (proved by Koishi Chan).

  A "good set" B ⊆ X is one that intersects every A ∈ F (B ∩ A ≠ ∅)
  but contains no A ∈ F (A ⊄ B). The existence of a good set is
  equivalent to Property B (2-colorability) of the family.

  This formalization:
  I.   Defines set families, uniformity, good sets, Property B
  II.  Proves equivalence of good sets and 2-colorability
  III. Proves base cases (empty family, singleton family)
  IV.  States the main conjecture (exponential abundance)
  V.   Axiomatizes Koishi Chan's affirmative answer
-/
import Mathlib

noncomputable section

namespace Erdos1027

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- A set family over α is a finset of finsets. -/
abbrev SetFamily (α : Type*) := Finset (Finset α)

/-- The ground set: union of all sets in the family. -/
def familyUnion (F : SetFamily α) : Finset α :=
  F.sup id

/-- F is n-uniform if every set in F has cardinality n. -/
def IsNUniform (F : SetFamily α) (n : ℕ) : Prop :=
  ∀ A ∈ F, A.card = n

/-- B intersects every set in F. -/
def IntersectsAll (B : Finset α) (F : SetFamily α) : Prop :=
  ∀ A ∈ F, (B ∩ A).Nonempty

/-- B contains no set in F. -/
def ContainsNone (B : Finset α) (F : SetFamily α) : Prop :=
  ∀ A ∈ F, ¬A ⊆ B

/-- A good set intersects every member of F but contains none. -/
def IsGoodSet (B : Finset α) (F : SetFamily α) : Prop :=
  IntersectsAll B F ∧ ContainsNone B F

/-- The collection of all good subsets of the ground set X = ∪F. -/
def goodSets (F : SetFamily α) : Finset (Finset α) :=
  (familyUnion F).powerset.filter (fun B => decide (IsGoodSet B F))

/-- Property B: the family has at least one good set. -/
def HasPropertyB (F : SetFamily α) : Prop :=
  ∃ B ⊆ familyUnion F, IsGoodSet B F

-- ============================================================
-- SECTION II: Property B and 2-Colorability
-- ============================================================

/-- A proper 2-coloring of X with respect to F: a function f : α → Bool
    such that no A ∈ F is monochromatic (all true or all false). -/
def IsProper2Coloring (f : α → Bool) (F : SetFamily α) : Prop :=
  ∀ A ∈ F, (∃ x ∈ A, f x = true) ∧ (∃ x ∈ A, f x = false)

/-- F is 2-colorable if it admits a proper 2-coloring. -/
def Is2Colorable (F : SetFamily α) : Prop :=
  ∃ f : α → Bool, IsProper2Coloring f F

/-- A good set B induces a proper 2-coloring: color x true iff x ∈ B. -/
theorem propertyB_implies_2colorable (F : SetFamily α)
    (hF : HasPropertyB F) : Is2Colorable F := by
  obtain ⟨B, _, hB_int, hB_none⟩ := hF
  refine ⟨fun x => x ∈ B, fun A hA => ⟨?_, ?_⟩⟩
  · -- B intersects A: ∃ x ∈ A, x ∈ B
    obtain ⟨x, hx⟩ := hB_int A hA
    exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
  · -- A ⊄ B: ∃ x ∈ A, x ∉ B
    have h := hB_none A hA
    rw [Finset.not_subset] at h
    obtain ⟨x, hxA, hxB⟩ := h
    exact ⟨x, hxA, by simp [hxB]⟩

/-- A proper 2-coloring induces a good set (the "true" class). -/
theorem coloring_implies_propertyB (F : SetFamily α)
    (hF : Is2Colorable F) (hne : ∀ A ∈ F, A.Nonempty)
    (hsub : ∀ A ∈ F, A ⊆ familyUnion F) :
    HasPropertyB F := by
  obtain ⟨f, hf⟩ := hF
  refine ⟨(familyUnion F).filter (fun x => f x = true), Finset.filter_subset _ _, ?_, ?_⟩
  · -- Intersects all: for each A, ∃ x ∈ A with f x = true
    intro A hA
    obtain ⟨x, hxA, hfx⟩ := (hf A hA).1
    exact ⟨x, Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨hsub A hA hxA, hfx⟩, hxA⟩⟩
  · -- Contains none: for each A, ∃ x ∈ A with f x = false
    intro A hA hsub_A
    obtain ⟨x, hxA, hfx⟩ := (hf A hA).2
    have := hsub_A hxA
    rw [Finset.mem_filter] at this
    simp [hfx] at this

-- ============================================================
-- SECTION III: Base Cases
-- ============================================================

/-- The empty family has Property B: every subset is good. -/
theorem empty_family_propertyB :
    HasPropertyB (∅ : SetFamily α) := by
  refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
  · intro A hA; exact absurd hA (Finset.not_mem_empty A)
  · intro A hA; exact absurd hA (Finset.not_mem_empty A)

/-- For the empty family, every subset of the (empty) ground set is good. -/
theorem empty_family_all_good (B : Finset α) :
    IsGoodSet B (∅ : SetFamily α) :=
  ⟨fun A hA => absurd hA (Finset.not_mem_empty A),
   fun A hA => absurd hA (Finset.not_mem_empty A)⟩

/-- A singleton family {A} with |A| ≥ 2 has Property B.
    Any single-element subset {x} with x ∈ A is a good set:
    it intersects A (contains x) but doesn't contain A (|{x}| < |A|). -/
theorem singleton_family_propertyB (A : Finset α) (hA : 2 ≤ A.card) :
    HasPropertyB ({A} : SetFamily α) := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  refine ⟨{x}, ?_, ?_, ?_⟩
  · -- {x} ⊆ familyUnion {A}
    intro y hy
    rw [Finset.mem_singleton.mp hy]
    show x ∈ familyUnion {A}
    simp [familyUnion, Finset.sup_singleton, hx]
  · -- Intersects all
    intro S hS
    rw [Finset.mem_singleton.mp hS]
    exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_singleton.mpr rfl, hx⟩⟩
  · -- Contains none
    intro S hS hsub
    rw [Finset.mem_singleton.mp hS] at hsub
    have := Finset.card_le_card hsub
    simp at this
    omega

-- ============================================================
-- SECTION IV: Good Set Counting
-- ============================================================

/-- The number of good subsets of the ground set. -/
def goodSetCount (F : SetFamily α) : ℕ :=
  (goodSets F).card

/-- The density of good sets: |good| / 2^|X|. -/
def goodSetDensity (F : SetFamily α) : ℚ :=
  goodSetCount F / 2 ^ (familyUnion F).card

-- ============================================================
-- SECTION V: The Main Conjecture and Solution
-- ============================================================

/-- **Erdős Problem #1027 (Conjecture)**: For every c > 0, there exists
    δ = δ(c) > 0 and N such that for all n ≥ N, every n-uniform family F
    with |F| ≤ c · 2^n has at least δ · 2^|X| good subsets of X = ∪F.

    This is the quantitative supersaturation of Property B. -/
axiom erdos_1027_conjecture :
  ∀ (c : ℝ) (_ : 0 < c), ∃ (δ : ℝ) (_ : 0 < δ), ∃ (N : ℕ),
    ∀ (n : ℕ) (_ : N ≤ n)
      (α : Type*) [DecidableEq α] [Fintype α]
      (F : SetFamily α) (_ : IsNUniform F n) (_ : (F.card : ℝ) ≤ c * 2 ^ n),
    δ * 2 ^ (familyUnion F).card ≤ (goodSetCount F : ℝ)

/-- **Koishi Chan's Theorem**: The conjecture holds. Every bounded n-uniform
    family has a constant fraction of good subsets. -/
axiom erdos_1027_solution :
  ∀ (c : ℝ) (_ : 0 < c), ∃ (δ : ℝ) (_ : 0 < δ), ∃ (N : ℕ),
    ∀ (n : ℕ) (_ : N ≤ n)
      (α : Type*) [DecidableEq α] [Fintype α]
      (F : SetFamily α) (_ : IsNUniform F n) (_ : (F.card : ℝ) ≤ c * 2 ^ n),
    δ * 2 ^ (familyUnion F).card ≤ (goodSetCount F : ℝ)

/-- The conjecture is solved: it follows directly from Koishi Chan's theorem. -/
theorem erdos_1027_solved : (∀ (c : ℝ) (_ : 0 < c), ∃ (δ : ℝ) (_ : 0 < δ), ∃ (N : ℕ),
    ∀ (n : ℕ) (_ : N ≤ n)
      (α : Type*) [DecidableEq α] [Fintype α]
      (F : SetFamily α) (_ : IsNUniform F n) (_ : (F.card : ℝ) ≤ c * 2 ^ n),
    δ * 2 ^ (familyUnion F).card ≤ (goodSetCount F : ℝ)) :=
  erdos_1027_solution

-- ============================================================
-- SECTION VI: Connection to Property B (Problem #901)
-- ============================================================

/-- Property B follows from the abundance result: if there are δ·2^|X| > 0
    good sets, then at least one good set exists. -/
theorem abundance_implies_propertyB (F : SetFamily α)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hcount : 0 < goodSetCount F) :
    HasPropertyB F := by
  have := Finset.card_pos.mp hcount
  obtain ⟨B, hB⟩ := this
  simp [goodSets] at hB
  obtain ⟨hBsub, hBgood⟩ := hB
  exact ⟨B, Finset.mem_powerset.mp hBsub, by
    rw [IsGoodSet] at hBgood ⊢
    exact hBgood⟩

/- ## Summary

**Problem**: Erdős #1027 — abundance of good sets for bounded n-uniform families.

**Formalization**: ~200 lines across 6 sections.

**Proved (sorry-free)**:
- `propertyB_implies_2colorable`: good set → proper 2-coloring
- `coloring_implies_propertyB`: proper 2-coloring → good set
- `empty_family_propertyB`: empty family has Property B
- `empty_family_all_good`: every subset is good for ∅
- `singleton_family_propertyB`: singleton family with |A| ≥ 2 has Property B
- `abundance_implies_propertyB`: abundance → Property B

**Axiomatized (2 axioms)**:
- `erdos_1027_conjecture`: the conjecture statement
- `erdos_1027_solution`: Koishi Chan's affirmative answer

**Status**: axiomatized (2 axioms encoding the solved conjecture)
-/

end Erdos1027

end
