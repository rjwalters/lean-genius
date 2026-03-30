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

/-- **Erdős Problem #1027 (Conjecture Statement)**: For every c > 0, there
    exists δ = δ(c) > 0 and N such that for all n ≥ N, every n-uniform family
    F with |F| ≤ c · 2^n has at least δ · 2^|X| good subsets of X = ∪F.

    This is the quantitative supersaturation of Property B. Defined as a Prop
    rather than an axiom — the actual solution is the axiom below. -/
def Erdos1027Statement : Prop :=
  ∀ (c : ℝ) (_ : 0 < c), ∃ (δ : ℝ) (_ : 0 < δ), ∃ (N : ℕ),
    ∀ (n : ℕ) (_ : N ≤ n)
      (α : Type*) [DecidableEq α] [Fintype α]
      (F : SetFamily α) (_ : IsNUniform F n) (_ : (F.card : ℝ) ≤ c * 2 ^ n),
    δ * 2 ^ (familyUnion F).card ≤ (goodSetCount F : ℝ)

/-- **Koishi Chan's Theorem**: The conjecture holds. Every bounded n-uniform
    family has a constant fraction of good subsets.

    This is the single axiom encoding the external mathematical result. -/
axiom erdos_1027_solution : Erdos1027Statement

/-- The conjecture is solved: it follows directly from Koishi Chan's theorem. -/
theorem erdos_1027_solved : Erdos1027Statement :=
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

-- ============================================================
-- SECTION VII: Erdős Classical Bound (1963)
-- ============================================================

/-- A coloring is monochromatic on A if all elements get the same color. -/
def IsMonochromatic (f : α → Bool) (A : Finset α) : Prop :=
  (∀ x ∈ A, f x = true) ∨ (∀ x ∈ A, f x = false)

instance (f : α → Bool) (A : Finset α) :
    Decidable (IsMonochromatic f A) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The set of functions α → Bool constantly b on A has at most 2^(|α| - |A|)
    elements: each element outside A is free, elements in A are fixed to b. -/
lemma card_constOn_le (A : Finset α) (b : Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = b)).card
    ≤ 2 ^ (Fintype.card α - A.card) := by
  -- Inject constrained functions into (↑(univ \ A) → Bool) via restriction.
  -- A function satisfying ∀ x ∈ A, f x = b is determined by its values on Aᶜ.
  set S := Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = b)
  set Ac := Finset.univ \ A
  -- The restriction map f ↦ (f ∘ Subtype.val : Ac → Bool) is injective on S
  have hinj : Set.InjOn (fun f : α → Bool => fun (x : Ac) => f x.1) ↑S := by
    intro f₁ hf₁ f₂ hf₂ heq
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ A
    · rw [hf₁ x hx, hf₂ x hx]
    · have hxAc : x ∈ Ac := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      exact congr_fun heq ⟨x, hxAc⟩
  -- |S| ≤ |Ac → Bool| = 2^|Ac| = 2^(|α| - |A|)
  calc S.card
      ≤ (Finset.univ : Finset (Ac → Bool)).card :=
        Finset.card_le_card_of_injOn (fun f (x : Ac) => f x.1)
          (fun _ _ => Finset.mem_univ _) hinj
    _ = Fintype.card (Ac → Bool) := Finset.card_univ
    _ = 2 ^ Fintype.card Ac := by rw [Fintype.card_fun, Fintype.card_bool]
    _ = 2 ^ Ac.card := by rw [Fintype.card_coe]
    _ = 2 ^ (Fintype.card α - A.card) := by
        congr 1; rw [Ac, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]

/-- Monochromatic colorings on A number at most 2 · 2^(|α| - |A|):
    at most 2^(|α| - |A|) for all-true plus 2^(|α| - |A|) for all-false. -/
lemma card_monochromatic_le (A : Finset α) :
    (Finset.univ.filter (fun f : α → Bool => IsMonochromatic f A)).card
    ≤ 2 * 2 ^ (Fintype.card α - A.card) := by
  calc (Finset.univ.filter (fun f => IsMonochromatic f A)).card
      ≤ (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = true) ∪
         Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = false)).card := by
        apply Finset.card_le_card
        intro f
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
                    IsMonochromatic]
        exact id
    _ ≤ (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = true)).card +
        (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = false)).card :=
      Finset.card_union_le _ _
    _ ≤ 2 ^ (Fintype.card α - A.card) + 2 ^ (Fintype.card α - A.card) := by
        linarith [card_constOn_le A true, card_constOn_le A false]
    _ = 2 * 2 ^ (Fintype.card α - A.card) := by ring

/-- **Erdős Classical Bound (1963)**: If F is a family of sets where every
    member has size ≥ t and |F| · 2 < 2^t, then F is 2-colorable.

    This is the first application of the probabilistic method in combinatorics.
    Among all 2^|α| colorings, the number making some set monochromatic is
    less than 2^|α|, so a proper coloring must exist. -/
theorem erdos_classical_bound (F : SetFamily α) (t : ℕ)
    (hsize : ∀ A ∈ F, t ≤ A.card)
    (hbound : F.card * 2 < 2 ^ t) :
    Is2Colorable F := by
  -- Trivial case: F empty
  by_cases hFne : F = ∅
  · exact ⟨fun _ => true, fun A hA => absurd hA (hFne ▸ Finset.not_mem_empty A)⟩
  -- For nonempty F: t ≤ |α|
  have ht_le : t ≤ Fintype.card α := by
    obtain ⟨A, hA⟩ := Finset.nonempty_of_ne_empty hFne
    exact le_trans (hsize A hA) (Finset.card_le_univ A)
  -- Bad colorings: those making some A ∈ F monochromatic
  set bad := F.biUnion (fun A => Finset.univ.filter
    (fun f : α → Bool => IsMonochromatic f A)) with hbad_def
  -- Union bound: |bad| ≤ ∑_A |mono(A)| ≤ |F| · (2 · 2^(n-t))
  have hbad_bound : bad.card ≤ F.card * (2 * 2 ^ (Fintype.card α - t)) := by
    calc bad.card
        ≤ F.sum (fun A => (Finset.univ.filter
            (fun f : α → Bool => IsMonochromatic f A)).card) :=
          Finset.card_biUnion_le
      _ ≤ F.sum (fun _ => 2 * 2 ^ (Fintype.card α - t)) := by
          apply Finset.sum_le_sum
          intro A hA
          calc _ ≤ 2 * 2 ^ (Fintype.card α - A.card) := card_monochromatic_le A
            _ ≤ 2 * 2 ^ (Fintype.card α - t) := by
              have : Fintype.card α - A.card ≤ Fintype.card α - t := by
                have h1 := hsize A hA; have h2 := Finset.card_le_univ A; omega
              exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) this)
      _ = F.card * (2 * 2 ^ (Fintype.card α - t)) := by
          simp [Finset.sum_const, smul_eq_mul]
  -- |bad| < 2^n = |total colorings|
  have hbad_lt : bad.card < 2 ^ Fintype.card α := by
    have hpos : 0 < 2 ^ (Fintype.card α - t) := pow_pos (by norm_num) _
    calc bad.card
        ≤ F.card * (2 * 2 ^ (Fintype.card α - t)) := hbad_bound
      _ = F.card * 2 * 2 ^ (Fintype.card α - t) := by ring
      _ < 2 ^ t * 2 ^ (Fintype.card α - t) :=
          mul_lt_mul_of_pos_right hbound hpos
      _ = 2 ^ Fintype.card α := by rw [← pow_add]; congr 1; omega
  -- Since |bad| < |total|, there exists a non-bad coloring
  have hgood : ∃ f : α → Bool, f ∉ bad := by
    by_contra h
    push_neg at h
    have : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at hbad_lt
    exact lt_irrefl _ hbad_lt
  obtain ⟨f, hf⟩ := hgood
  -- f is not monochromatic on any A ∈ F, hence a proper 2-coloring
  refine ⟨f, fun A hA => ?_⟩
  have hfA : ¬ IsMonochromatic f A := by
    intro h
    exact hf (Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_filter.mpr ⟨Finset.mem_univ f, h⟩⟩)
  simp only [IsMonochromatic, not_or] at hfA
  obtain ⟨hnt, hnf⟩ := hfA
  push_neg at hnt hnf
  obtain ⟨y, hyA, hyf⟩ := hnt
  obtain ⟨x, hxA, hxf⟩ := hnf
  exact ⟨⟨x, hxA, by cases h : f x <;> simp_all⟩,
         ⟨y, hyA, by cases h : f y <;> simp_all⟩⟩

/- ## Summary

**Problem**: Erdős #1027 — abundance of good sets for bounded n-uniform families.

**Formalization**: ~320 lines across 7 sections.

**Proved (sorry-free)**:
- `propertyB_implies_2colorable`: good set → proper 2-coloring
- `coloring_implies_propertyB`: proper 2-coloring → good set
- `empty_family_propertyB`: empty family has Property B
- `empty_family_all_good`: every subset is good for ∅
- `singleton_family_propertyB`: singleton family with |A| ≥ 2 has Property B
- `abundance_implies_propertyB`: abundance → Property B
- `card_monochromatic_le`: bound on monochromatic colorings (modulo `card_constOn_le`)
- `erdos_classical_bound`: Erdős 1963 probabilistic method bound (modulo `card_constOn_le`)

**Axiomatized (1 axiom)**:
- `erdos_1027_solution`: Koishi Chan's affirmative answer (= `Erdos1027Statement`)

**Open sorries (1)**:
- `card_constOn_le`: counting functions constant on a subset (routine combinatorics)

**Status**: axiomatized (1 axiom encoding the solved conjecture, 0 sorries)
-/

end Erdos1027

end
