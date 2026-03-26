import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

/-
# Erdős Problem #1167 - Partition Relations on Cardinals

## Problem Statement (Erdős-Hajnal-Rado)

For finite r ≥ 2, infinite cardinal λ, and cardinals κ_α (for all α < γ), does

  2^λ → (κ_α + 1)^{r+1}_{α < γ}

imply

  λ → (κ_α)^r_{α < γ}?

## Background

The partition relation κ → (λ_α)^r_{α < γ} means: for every coloring
f : [κ]^r → γ (where [κ]^r is the set of r-element subsets of κ), there
exist α < γ and H ⊆ κ with |H| ≥ λ_α such that f is constant with value
α on all r-element subsets of H (a monochromatic set).

When κ_α is infinite, κ_α + 1 = κ_α in cardinal arithmetic, so the "+1"
is only meaningful for finite cardinals.

This is a deep question in infinitary combinatorics relating partition
properties at consecutive exponents. It was posed by Erdős, Hajnal, and
Rado in their foundational work on partition calculus (1956).

## Status: OPEN

## Reference: [Va99, 7.79] - A problem of Erdős, Hajnal, and Rado

## Known Partial Results
- The Erdős-Rado theorem (1956) establishes the "stepping up" direction
- The infinite Ramsey theorem provides consistency for the ℵ₀ case
- For 2 colors and pairs (r=2), the Erdős-Rado theorem gives the prototype

## Formalization
- Partition relations defined for cardinals using set-theoretic colorings
- Structural lemmas proved (one-color, monotonicity, subsets, cardinal arithmetic)
- Main conjecture stated as axiom (OPEN)
- Known results (infinite Ramsey, Erdős-Rado) as axioms
- 6 new lemmas: zero target, indexed monotonicity, subset mono, infinite targets,
  2^λ infiniteness, Erdős-Rado weakening
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace Erdos1167

open Cardinal Set

-- An r-element subset of a type α
def RSubset (α : Type*) (r : ℕ) : Type* :=
  { s : Finset α // s.card = r }

-- A coloring of r-element subsets of a type into γ colors
def Coloring (α : Type*) (r : ℕ) (γ : Type*) :=
  RSubset α r → γ

-- A set H is monochromatic under coloring f with color c:
-- every r-element subset drawn from H gets color c
def IsMonochromatic {α : Type*} {r : ℕ} {γ : Type*}
    (f : Coloring α r γ) (H : Set α) (c : γ) : Prop :=
  ∀ (s : RSubset α r), (↑s.val : Set α) ⊆ H → f s = c

-- The partition relation κ → (λ)^r_γ:
-- Every γ-coloring of r-subsets of a set of size κ has a
-- monochromatic set of size ≥ λ in some color
def PartitionRelation (κ λ_target : Cardinal) (r : ℕ) (γ : Cardinal) : Prop :=
  ∀ (α : Type*) (_ : #α = κ)
    (β : Type*) (_ : #β = γ)
    (f : Coloring α r β),
    ∃ (c : β) (H : Set α),
      IsMonochromatic f H c ∧ #H ≥ λ_target

-- The indexed partition relation κ → (κ_i)^r_{i < γ}:
-- For every coloring into γ colors, there exists a color i < γ
-- with a monochromatic set of size ≥ κ_i
def IndexedPartitionRelation (κ : Cardinal) (targets : Ordinal → Cardinal)
    (r : ℕ) (γ : Ordinal) : Prop :=
  ∀ (α : Type*) (_ : #α = κ)
    (β : Type*) (_ : #β = Ordinal.card γ)
    (f : Coloring α r β),
    ∃ (c : β) (H : Set α) (i : Ordinal),
      i < γ ∧ IsMonochromatic f H c ∧ #H ≥ targets i

/-
## Section 1: Structural Properties of Partition Relations

These are basic properties that follow directly from the definitions.
All are fully proved with no axioms.
-/

-- For 1 color, κ → (κ)^r_1 always holds
-- (with one color, the whole set is monochromatic)
theorem partition_one_color (κ : Cardinal) (r : ℕ) :
    PartitionRelation κ κ r 1 := by
  intro α hα β hβ f
  -- β has exactly one element, so any two values are equal
  have : Subsingleton β := by
    rwa [Cardinal.eq_one_iff_unique] at hβ
  -- β is nonempty (has cardinality 1)
  have hne : Nonempty β := by
    rwa [Cardinal.mk_ne_zero_iff, ← hβ]
    exact one_ne_zero
  obtain ⟨c⟩ := hne
  exact ⟨c, univ, fun s _ => Subsingleton.elim _ _, by simp [hα]⟩

-- Monotonicity in target: if κ → (λ)^r_γ and λ' ≤ λ, then κ → (λ')^r_γ
theorem partition_monotone_target {κ λ_target λ' : Cardinal} {r : ℕ}
    {γ : Cardinal}
    (h : PartitionRelation κ λ_target r γ) (hle : λ' ≤ λ_target) :
    PartitionRelation κ λ' r γ := by
  intro α hα β hβ f
  obtain ⟨c, H, hmono, hcard⟩ := h α hα β hβ f
  exact ⟨c, H, hmono, le_trans hle hcard⟩

-- For r > 0, the empty set is vacuously monochromatic: κ → (0)^r_γ
-- (no r-element subset can be drawn from ∅ when r > 0)
theorem partition_zero_target (κ : Cardinal) (r : ℕ) (hr : 0 < r)
    (γ : Cardinal) (hγ : γ ≠ 0) :
    PartitionRelation κ 0 r γ := by
  intro α _hα β hβ f
  have hne : Nonempty β := by
    rwa [Cardinal.mk_ne_zero_iff, ← hβ]
  obtain ⟨c⟩ := hne
  refine ⟨c, ∅, fun s hs => ?_, by simp⟩
  exfalso
  have hempty : (↑s.val : Set α) ⊆ ∅ := hs
  rw [Set.subset_empty_iff] at hempty
  simp [Finset.coe_eq_empty] at hempty
  have hcard := s.2
  rw [hempty] at hcard
  simp at hcard
  omega

-- Monotonicity of indexed partition: weakening targets
-- If κ → (κ_i)^r_{i<γ} and targets' i ≤ targets i for all i,
-- then κ → (κ'_i)^r_{i<γ}
theorem indexed_partition_monotone_targets {κ : Cardinal}
    {targets targets' : Ordinal → Cardinal} {r : ℕ} {γ : Ordinal}
    (h : IndexedPartitionRelation κ targets r γ)
    (hle : ∀ i, i < γ → targets' i ≤ targets i) :
    IndexedPartitionRelation κ targets' r γ := by
  intro α hα β hβ f
  obtain ⟨c, H, i, hi, hmono, hcard⟩ := h α hα β hβ f
  exact ⟨c, H, i, hi, hmono, le_trans (hle i hi) hcard⟩

-- Subsets of monochromatic sets are monochromatic
theorem isMonochromatic_subset {α : Type*} {r : ℕ} {γ : Type*}
    {f : Coloring α r γ} {H H' : Set α} {c : γ}
    (hmono : IsMonochromatic f H c) (hsub : H' ⊆ H) :
    IsMonochromatic f H' c := by
  intro s hs
  exact hmono s (Set.Subset.trans hs hsub)

/-
## Section 2: Cardinal Arithmetic for Partition Relations

Key facts about cardinal arithmetic that are relevant to the conjecture.
The "+1" operation in the conjecture is trivial for infinite cardinals
but meaningful for finite ones.
-/

-- For infinite κ, κ + 1 = κ in cardinal arithmetic
-- This shows the "+1" in the conjecture is only relevant for finite targets
theorem infinite_card_add_one (κ : Cardinal) (hκ : ℵ₀ ≤ κ) :
    κ + 1 = κ := by
  have h1 : (1 : Cardinal) ≤ ℵ₀ := by exact one_le_aleph0
  have := Cardinal.add_eq_self hκ
  rw [add_comm] at this ⊢
  calc 1 + κ ≤ κ + κ := by exact add_le_add_right (le_trans h1 hκ) κ
    _ = κ := this

-- For natural numbers, κ + 1 is genuinely larger
theorem finite_card_add_one (n : ℕ) :
    (n : Cardinal) + 1 = ((n + 1 : ℕ) : Cardinal) := by
  push_cast
  ring

-- When all targets are infinite, the hypothesis of the conjecture simplifies:
-- 2^λ → (κ_α + 1)^{r+1} is equivalent to 2^λ → (κ_α)^{r+1}
-- because κ_α + 1 = κ_α for infinite κ_α
theorem conjecture_simplifies_infinite_targets
    (r : ℕ) (_hr : r ≥ 2)
    (λ_card : Cardinal.{u}) (_hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u})
    (htargets : ∀ i, i < γ → ℵ₀ ≤ targets i)
    (h : IndexedPartitionRelation (2 ^ λ_card) targets (r + 1) γ) :
    IndexedPartitionRelation (2 ^ λ_card)
      (fun α => targets α + 1) (r + 1) γ := by
  intro α hα β hβ f
  obtain ⟨c, H, i, hi, hmono, hcard⟩ := h α hα β hβ f
  refine ⟨c, H, i, hi, hmono, ?_⟩
  rw [infinite_card_add_one (targets i) (htargets i hi)]
  exact hcard

-- For infinite λ, 2^λ is also infinite (and strictly larger)
-- This is relevant because the conjecture's hypothesis involves 2^λ
theorem two_pow_infinite (λ_card : Cardinal) (hλ : ℵ₀ ≤ λ_card) :
    ℵ₀ ≤ 2 ^ λ_card := by
  calc ℵ₀ ≤ λ_card := hλ
    _ ≤ 2 ^ λ_card := Cardinal.cantor λ_card

/-
## Section 3: The Erdős-Hajnal-Rado Conjecture (#1167) and Known Results

The main conjecture asks whether partition properties for (r+1)-tuples
on 2^λ can be stepped down to r-tuples on λ.

Known results:
- Erdős-Rado theorem (1956): (2^κ)⁺ → (κ⁺)²_κ (stepping UP)
- Infinite Ramsey theorem: ℵ₀ → (ℵ₀)^r_k for finite r, k
- The conjecture is consistent with both of these

These known results remain as axioms since they require substantial
proof infrastructure (transfinite recursion, Ramsey-style arguments)
not yet available in Mathlib's partition calculus.
-/

-- The Erdős-Hajnal-Rado stepping-down conjecture
-- OPEN: This remains unresolved
axiom erdos_1167_conjecture
    (r : ℕ) (hr : r ≥ 2)
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u}) :
    IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) (r + 1) γ →
    IndexedPartitionRelation λ_card targets r γ

-- The infinite Ramsey theorem: ℵ₀ → (ℵ₀)^r_k for all finite r, k
-- Known result (proved by Ramsey 1929 for finite case,
-- extended to infinite by Erdős-Rado)
axiom infinite_ramsey (r k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ r k

-- Erdős-Rado theorem: (2^κ)⁺ → (κ⁺)²_κ
-- The classical result from "A partition calculus in set theory" (1956)
axiom erdos_rado_theorem (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    PartitionRelation (Order.succ (2 ^ κ)) (Order.succ κ) 2 κ

/-
## Section 4: Consequences and Consistency Checks
-/

-- The r = 2 case follows from the main conjecture
theorem erdos_1167_r2_case
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u})
    (h : IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) 3 γ) :
    IndexedPartitionRelation λ_card targets 2 γ :=
  erdos_1167_conjecture 2 (by omega) λ_card hλ γ targets h

-- General r case: instantiation of the conjecture for any specific r ≥ 2
theorem erdos_1167_general_case (r : ℕ) (hr : r ≥ 2)
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u})
    (h : IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) (r + 1) γ) :
    IndexedPartitionRelation λ_card targets r γ :=
  erdos_1167_conjecture r hr λ_card hλ γ targets h

-- Consistency check: the conjecture is consistent with infinite Ramsey
-- ℵ₀ → (ℵ₀)²_2 is known true (infinite Ramsey theorem)
theorem conjecture_consistent_aleph0 :
    PartitionRelation ℵ₀ ℵ₀ 2 2 :=
  infinite_ramsey 2 2

-- The infinite Ramsey theorem for pairs with k colors
theorem ramsey_pairs (k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ 2 k :=
  infinite_ramsey 2 k

-- The infinite Ramsey theorem for triples with 2 colors
theorem ramsey_triples_two_colors :
    PartitionRelation ℵ₀ ℵ₀ 3 2 :=
  infinite_ramsey 3 2

-- Weakening the Erdős-Rado theorem to a smaller target:
-- Since (2^κ)⁺ → (κ⁺)²_κ, we also have (2^κ)⁺ → (κ)²_κ
-- (monotonicity in target, since κ ≤ κ⁺)
theorem erdos_rado_weakened (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    PartitionRelation (Order.succ (2 ^ κ)) κ 2 κ := by
  apply partition_monotone_target (erdos_rado_theorem κ hκ)
  exact Order.le_succ κ

/-
## Section 5: Provable Cases of the Infinite Ramsey Theorem

The r ≤ 1 cases of the infinite Ramsey theorem follow from first
principles without the full axiom. For r = 0, ∅ is the unique
0-element subset, so any coloring is trivially monochromatic.
For r = 1, the infinite pigeonhole principle applies: coloring ℵ₀
elements with finitely many colors forces at least one color class
to be infinite.

This demonstrates that the infinite_ramsey axiom is only needed
for the non-trivial case r ≥ 2, where Ramsey-style arguments
involving transfinite recursion are required.
-/

-- Infinite Ramsey for r = 0: trivially true since ∅ is the unique
-- 0-element subset, making any set vacuously monochromatic
theorem infinite_ramsey_zero (k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ 0 ↑k := by
  intro α hα β hβ f
  by_cases hne : Nonempty β
  · -- β nonempty: the color of ∅ determines the monochromatic color
    let s0 : RSubset α 0 := ⟨∅, Finset.card_empty⟩
    exact ⟨f s0, Set.univ, fun s _ =>
      congr_arg f (Subtype.ext (Finset.card_eq_zero.mp s.2)), by simp [hα]⟩
  · -- β empty: no coloring from a nonempty type to ∅ exists, vacuously true
    exact absurd (⟨f ⟨∅, Finset.card_empty⟩⟩ : Nonempty β) hne

-- Infinite Ramsey for r = 1: the infinite pigeonhole principle
-- Coloring ℵ₀ elements with k ≥ 1 colors forces an infinite color class
theorem infinite_ramsey_one (k : ℕ) (hk : k ≥ 1) :
    PartitionRelation ℵ₀ ℵ₀ 1 ↑k := by
  intro α hα β hβ f
  -- Map each element to the color of its singleton subset
  let g : α → β := fun x => f ⟨{x}, Finset.card_singleton x⟩
  -- α is infinite (ℵ₀ elements)
  haveI hInfα : Infinite α := by
    by_contra h
    simp only [not_infinite] at h
    exact absurd (Cardinal.lt_aleph0_iff_finite.mpr h)
      (not_lt.mpr (le_of_eq hα.symm))
  -- β is finite (k elements)
  haveI hFinβ : Finite β := Cardinal.lt_aleph0_iff_finite.mp
    (hβ ▸ Cardinal.nat_lt_aleph0 k)
  -- By infinite pigeonhole, some fiber of g is infinite
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber g
  -- The infinite fiber g⁻¹{c} is our monochromatic set
  refine ⟨c, g ⁻¹' {c}, fun s hs => ?_, ?_⟩
  · -- Monochromatic: every 1-element subset from the fiber has color c
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.2
    -- x ∈ g⁻¹{c} since {x} ⊆ g⁻¹{c}
    have hxH : x ∈ g ⁻¹' {c} := hs (by simp [hx])
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxH
    -- f(s) = f({x}) = g(x) = c
    rw [show s = ⟨{x}, Finset.card_singleton x⟩ from Subtype.ext hx]
    exact hxH
  · -- The fiber has cardinality ≥ ℵ₀
    by_contra hlt
    simp only [not_le] at hlt
    haveI := Cardinal.lt_aleph0_iff_finite.mp hlt
    exact hc (Set.toFinite _)

end Erdos1167
