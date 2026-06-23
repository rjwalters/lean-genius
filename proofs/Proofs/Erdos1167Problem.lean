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
## Section 3: The Erdős-Hajnal-Rado Conjecture and Remaining Axioms

The main conjecture asks whether partition properties for (r+1)-tuples
on 2^λ can be stepped down to r-tuples on λ. The Erdős-Rado theorem
is a deep result about stepping UP that remains axiomatized.
-/

-- The Erdős-Hajnal-Rado stepping-down conjecture
-- OPEN: This remains unresolved
axiom erdos_1167_conjecture
    (r : ℕ) (hr : r ≥ 2)
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u}) :
    IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) (r + 1) γ →
    IndexedPartitionRelation λ_card targets r γ

-- Erdős-Rado theorem: (2^κ)⁺ → (κ⁺)²_κ
-- The classical result from "A partition calculus in set theory" (1956)
axiom erdos_rado_theorem (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    PartitionRelation (Order.succ (2 ^ κ)) (Order.succ κ) 2 κ

/-
## Section 4: The Infinite Ramsey Theorem (Proved)

We prove ℵ₀ → (ℵ₀)^r_k for all finite r, k. The proof proceeds
by induction on r:
- r = 0: trivial (unique 0-subset)
- r = 1: infinite pigeonhole principle
- r + 1: Ramsey's diagonal argument — fix a vertex v from the infinite
  set S, define a reduced r-coloring g(T) = f({v} ∪ T) on S \ {v},
  apply the IH to get an infinite monochromatic subset H, iterate this
  to build a sequence of (vertex, color) pairs, then extract an infinite
  monochromatic subsequence via pigeonhole on the finitely many colors.

This eliminates the previous `infinite_ramsey` axiom, reducing the
axiom count from 3 to 2.
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

-- The Ramsey step: given an infinite set S and an (r+1)-coloring f,
-- extract a vertex v ∈ S, a color c, and an infinite subset H ⊆ S \ {v}
-- that is monochromatic for the reduced coloring g(T) = f({v} ∪ T).
private lemma ramsey_step {α : Type*} [DecidableEq α] {β : Type*}
    {r k : ℕ} (hα : #α = ℵ₀)
    (f : Coloring α (r + 1) β) (hβ : #β = ↑k)
    (ih : PartitionRelation ℵ₀ ℵ₀ r ↑k)
    (S : Set α) (hS : Set.Infinite S) :
    ∃ (v : α) (c : β) (H : Set α),
      v ∈ S ∧ Set.Infinite H ∧ H ⊆ S ∧ v ∉ H ∧
      (∀ (T : Finset α), T.card = r → (↑T : Set α) ⊆ H → v ∉ T →
        f ⟨Finset.cons v T ‹v ∉ T›,
          by rw [Finset.card_cons]; omega⟩ = c) := by
  obtain ⟨v, hv⟩ := hS.nonempty
  have hS' : Set.Infinite (S \ {v}) := hS.diff (Set.finite_singleton v)
  have hS'_card : #↥(S \ {v}) = ℵ₀ := le_antisymm
    ((Cardinal.mk_subtype_le _).trans (le_of_eq hα))
    (Cardinal.infinite_iff.mp (Set.infinite_coe_iff.mpr hS'))
  -- Define reduced coloring on ↥(S \ {v}): maps r-subsets T to f({v} ∪ T)
  let emb : ↥(S \ {v}) ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  let g : Coloring ↥(S \ {v}) r β := fun s =>
    have hv_not : v ∉ s.val.map emb := by
      simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk]
      rintro ⟨⟨x, hx⟩, _, rfl⟩; exact hx.2 rfl
    f ⟨Finset.cons v (s.val.map emb) hv_not,
      by rw [Finset.card_cons, Finset.card_map, s.2]⟩
  -- Apply IH to get monochromatic subset of ↥(S \ {v})
  obtain ⟨c, H_sub, hH_mono, hH_card⟩ := ih ↥(S \ {v}) hS'_card β hβ g
  -- Map H_sub back to Set α
  have hH_inf : Set.Infinite H_sub :=
    Set.infinite_coe_iff.mpr (Cardinal.infinite_iff.mpr hH_card)
  refine ⟨v, c, Subtype.val '' H_sub, hv, hH_inf.image Subtype.val_injective.injOn,
    ?_, ?_, ?_⟩
  · -- Subtype.val '' H_sub ⊆ S
    rintro x ⟨⟨y, hy⟩, _, rfl⟩; exact hy.1
  · -- v ∉ Subtype.val '' H_sub
    rintro ⟨⟨y, hy⟩, _, rfl⟩; exact hy.2 rfl
  · -- Monochromaticity: for r-subsets T ⊆ H with v ∉ T, f(cons v T) = c
    intro T hT hT_sub hv_not_T
    -- Each element of T is in Subtype.val '' H_sub, hence in S \ {v}
    have hT_diff : ∀ x ∈ T, x ∈ S \ {v} := fun x hx => by
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hT_sub (Finset.mem_coe.mpr hx); exact hy
    -- Lift T to Finset ↥(S \ {v}): each x ∈ T maps to ⟨x, proof⟩
    let T' : Finset ↥(S \ {v}) := T.attach.map
      ⟨fun ⟨x, hx⟩ => ⟨x, hT_diff x hx⟩, fun ⟨a, _⟩ ⟨b, _⟩ h => by
        simp only [Subtype.mk.injEq] at h; exact Subtype.ext h⟩
    have hT'_card : T'.card = r := by
      simp only [T', Finset.card_map, Finset.card_attach]; exact hT
    -- T'.map emb = T (lifting then projecting recovers the original)
    have hT'_map : T'.map emb = T := by
      ext x; constructor
      · rintro ⟨⟨y, _⟩, ⟨⟨z, hz⟩, _, rfl⟩, rfl⟩; exact hz
      · intro hx
        exact ⟨⟨x, hT_diff x hx⟩,
          ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
    -- T' elements are in H_sub (by proof irrelevance on subtype proofs)
    have hT'_sub : (↑T' : Set ↥(S \ {v})) ⊆ H_sub := by
      intro ⟨y, hy⟩ hy_mem
      simp only [Finset.mem_coe, Finset.mem_map, Function.Embedding.coeFn_mk, T'] at hy_mem
      obtain ⟨⟨x, hx⟩, _, hxy⟩ := hy_mem
      simp only [Subtype.mk.injEq] at hxy
      obtain ⟨z, hz_mem, hz_val⟩ := hT_sub (Finset.mem_coe.mpr hx)
      -- z.val = x = y, so ⟨y, hy⟩ = z by proof irrelevance
      exact (show (⟨y, hy⟩ : ↥(S \ {v})) = z from
        Subtype.ext (hxy ▸ hz_val.symm)) ▸ hz_mem
    -- Apply monochromaticity of H_sub under g
    have hmono := hH_mono ⟨T', hT'_card⟩ hT'_sub
    -- g ⟨T', _⟩ = f ⟨cons v (T'.map emb) _, _⟩ = f ⟨cons v T _, _⟩ = c
    simp only [g] at hmono
    rw [hT'_map] at hmono
    -- The two RSubset values are equal by proof irrelevance
    convert hmono using 1
    exact Subtype.ext rfl

-- The full infinite Ramsey theorem: ℵ₀ → (ℵ₀)^r_k for all finite r, k.
-- Proved by induction on r with Ramsey's diagonal argument.
-- This replaces the previous axiom.
theorem infinite_ramsey (r k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ r ↑k := by
  induction r with
  | zero => exact infinite_ramsey_zero k
  | succ r ih =>
    intro α hα β hβ f
    haveI : DecidableEq α := Classical.dec _
    haveI : Infinite α := Cardinal.infinite_iff.mp (hα ▸ le_refl _)
    -- Handle k = 0: β is empty, no coloring can exist (vacuously true)
    by_cases hk : k = 0
    · subst hk; simp only [Nat.cast_zero] at hβ
      haveI : IsEmpty β := Cardinal.mk_eq_zero_iff.mp hβ
      -- f : RSubset α (r+1) → β with β empty — any application gives False
      -- Build one (r+1)-element finset of α (which is infinite)
      exfalso
      suffices ∃ s : Finset α, s.card = r + 1 by
        obtain ⟨s, hs⟩ := this; exact IsEmpty.elim inferInstance (f ⟨s, hs⟩)
      induction (r + 1) with
      | zero => exact ⟨∅, rfl⟩
      | succ n ih =>
        obtain ⟨s, hs⟩ := ih
        have ⟨x, hx⟩ : ∃ x, x ∉ s := by
          by_contra hall; push_neg at hall
          exact absurd (s.finite_toSet.subset (fun x _ => Finset.mem_coe.mpr (hall x)))
            Set.infinite_univ
        exact ⟨s.cons x hx, by rw [Finset.card_cons, hs]⟩
    · -- k ≥ 1: Ramsey's diagonal argument
      haveI : Finite β := Cardinal.lt_aleph0_iff_finite.mp
        (hβ ▸ Cardinal.nat_lt_aleph0 k)
      -- Step 1: The Ramsey step gives us a one-step extraction
      have step : ∀ S : Set α, Set.Infinite S →
          ∃ (v : α) (c : β) (H : Set α),
            v ∈ S ∧ Set.Infinite H ∧ H ⊆ S ∧ v ∉ H ∧
            (∀ T : Finset α, T.card = r → (↑T : Set α) ⊆ H → v ∉ T →
              f ⟨Finset.cons v T ‹_›, by rw [Finset.card_cons]; omega⟩ = c) :=
        fun S hS => ramsey_step hα f hβ ih S hS
      -- Step 2: Build the Ramsey sequence by iterating the step
      -- Helper: extract the monochromatic subset from the step
      let stepH (S : Set α) (hS : Set.Infinite S) : Set α :=
        (step S hS).choose_spec.choose_spec.choose
      let stepH_inf (S : Set α) (hS : Set.Infinite S) :
          Set.Infinite (stepH S hS) :=
        (step S hS).choose_spec.choose_spec.choose_spec.2.1
      -- Build state sequence via Nat.rec
      let rec stateRec : ℕ → { S : Set α // Set.Infinite S }
        | 0 => ⟨Set.univ, Set.infinite_univ⟩
        | n + 1 =>
          let ⟨S, hS⟩ := stateRec n
          ⟨stepH S hS, stepH_inf S hS⟩
      -- Extract vertex and color sequences
      let vertex : ℕ → α := fun n =>
        (step (stateRec n).1 (stateRec n).2).choose
      let color : ℕ → β := fun n =>
        (step (stateRec n).1 (stateRec n).2).choose_spec.choose
      -- Abbreviation for the step properties at step n
      let stepProps (n : ℕ) :=
        (step (stateRec n).1 (stateRec n).2).choose_spec.choose_spec.choose_spec
      -- Key property: stateRec (n+1) = stepH (stateRec n)
      have state_eq : ∀ n, (stateRec (n + 1)).1 = stepH (stateRec n).1 (stateRec n).2 := by
        intro n; rfl
      -- stateRec (n+1) ⊆ stateRec n
      have state_sub : ∀ n, (stateRec (n + 1)).1 ⊆ (stateRec n).1 := by
        intro n; rw [state_eq]; exact (stepProps n).2.2.1
      -- vertex n ∈ stateRec n
      have vertex_mem : ∀ n, vertex n ∈ (stateRec n).1 := by
        intro n; exact (stepProps n).1
      -- vertex n ∉ stateRec (n+1)
      have vertex_excluded : ∀ n, vertex n ∉ (stateRec (n + 1)).1 := by
        intro n; rw [state_eq]; exact (stepProps n).2.2.2.1
      -- Monochromaticity at each step
      have mono_at : ∀ n (T : Finset α), T.card = r →
          (↑T : Set α) ⊆ (stateRec (n + 1)).1 → vertex n ∉ T →
          f ⟨Finset.cons (vertex n) T ‹_›,
            by rw [Finset.card_cons]; omega⟩ = color n := by
        intro n T hT hTsub hvnT
        rw [state_eq] at hTsub
        exact (stepProps n).2.2.2.2 T hT hTsub hvnT
      -- Derived: state antitone (stateRec m ⊆ stateRec n for n ≤ m)
      have state_antitone : ∀ n m, n ≤ m → (stateRec m).1 ⊆ (stateRec n).1 := by
        intro n m h
        induction h with
        | refl => exact Set.Subset.refl _
        | step h ih => exact (state_sub _).trans ih
      -- vertex m ∈ stateRec n for n ≤ m
      have vertex_later : ∀ n m, n ≤ m → vertex m ∈ (stateRec n).1 := by
        intro n m h; exact state_antitone n m h (vertex_mem m)
      -- vertex is injective (vertex n ∉ stateRec(n+1) but vertex m ∈ stateRec(n+1) for m > n)
      have vertex_inj : Function.Injective vertex := by
        intro m n h
        by_contra hmn
        rcases Ne.lt_or_lt hmn with hlt | hlt
        · -- m < n: vertex n ∈ stateRec(m+1) but vertex m ∉ stateRec(m+1)
          exact vertex_excluded m (h ▸ vertex_later (m + 1) n hlt)
        · -- n < m: vertex m ∈ stateRec(n+1) but vertex n ∉ stateRec(n+1)
          exact vertex_excluded n (h.symm ▸ vertex_later (n + 1) m hlt)
      -- Step 3: Pigeonhole on colors (infinite sequence → finite codomain)
      haveI : Infinite ℕ := inferInstance
      obtain ⟨c_star, hc_star⟩ := Finite.exists_infinite_fiber color
      -- Step 4: The monochromatic set H = vertex '' {n | color n = c_star}
      let H_final := vertex '' (color ⁻¹' {c_star})
      have hH_inf : Set.Infinite H_final :=
        (Set.infinite_coe_iff.mpr hc_star).image vertex_inj.injOn
      refine ⟨c_star, H_final, ?_, ?_⟩
      · -- IsMonochromatic: every (r+1)-subset from H_final gets color c_star
        intro s hs
        -- Use Function.invFun to get a global index function (no membership dependency)
        let invV := Function.invFun vertex
        -- For x in range of vertex, invV recovers the index
        have invV_spec : ∀ n, invV (vertex n) = n :=
          fun n => vertex_inj (Function.invFun_eq ⟨n, rfl⟩)
        -- For x ∈ H_final, vertex (invV x) = x
        have invV_recover : ∀ x, x ∈ H_final → vertex (invV x) = x := by
          rintro _ ⟨n, _, rfl⟩; rw [invV_spec]; rfl
        -- For x ∈ H_final, color (invV x) = c_star
        have invV_color : ∀ x, x ∈ H_final → color (invV x) = c_star := by
          rintro _ ⟨n, hn, rfl⟩; rw [invV_spec]; exact hn
        -- s.val is nonempty (has r+1 ≥ 1 elements)
        have s_nonempty : s.val.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h
          have := s.2; rw [h, Finset.card_empty] at this; omega
        -- Find element of s.val with minimum invV value
        obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
          s.val.exists_min_image invV s_nonempty
        -- The pivot index n_min = invV x_min
        set n_min := invV x_min with n_min_def
        have hx_min_in_H : x_min ∈ H_final := hs (Finset.mem_coe.mpr hx_min_mem)
        have hpivot : vertex n_min = x_min := invV_recover x_min hx_min_in_H
        have hpivot_color : color n_min = c_star := invV_color x_min hx_min_in_H
        -- Decompose s.val = {x_min} ∪ rest where rest = s.val.erase x_min
        let rest := s.val.erase x_min
        have hrest_card : rest.card = r := by
          simp only [rest, Finset.card_erase_of_mem hx_min_mem, s.2]; omega
        -- All elements of rest have strictly larger index than n_min
        -- and hence lie in stateRec (n_min + 1)
        have hrest_sub : (↑rest : Set α) ⊆ (stateRec (n_min + 1)).1 := by
          intro y hy_rest
          have hy_mem : y ∈ s.val := Finset.mem_of_mem_erase hy_rest
          have hy_ne : y ≠ x_min := Finset.ne_of_mem_erase hy_rest
          have hy_in_H : y ∈ H_final := hs (Finset.mem_coe.mpr hy_mem)
          -- invV y ≥ invV x_min = n_min
          have hle : n_min ≤ invV y := hx_min_le y hy_mem
          -- invV y ≠ n_min (otherwise y = x_min, contradiction)
          have hne : invV y ≠ n_min := by
            intro heq
            have := invV_recover y hy_in_H  -- vertex (invV y) = y
            have := invV_recover x_min hx_min_in_H  -- vertex n_min = x_min
            exact hy_ne (vertex_inj (by rw [heq, n_min_def]; exact this ▸ ‹vertex (invV y) = y›))
          -- So invV y > n_min, i.e., invV y ≥ n_min + 1
          have hgt : n_min + 1 ≤ invV y := by omega
          -- vertex (invV y) = y ∈ stateRec (n_min + 1)
          have := vertex_later (n_min + 1) (invV y) hgt
          rwa [invV_recover y hy_in_H] at this
        -- vertex n_min ∉ rest (since x_min ∉ s.val.erase x_min)
        have hpivot_not : vertex n_min ∉ rest := hpivot ▸ Finset.not_mem_erase x_min s.val
        -- Apply monochromaticity at step n_min
        have hmono := mono_at n_min rest hrest_card hrest_sub hpivot_not
        -- Reconstruct: s.val = cons (vertex n_min) rest
        have hrecon : s.val = Finset.cons (vertex n_min) rest hpivot_not := by
          ext x; simp only [rest, Finset.mem_cons, Finset.mem_erase]
          constructor
          · intro hx
            by_cases hxv : x = vertex n_min
            · left; exact hxv
            · right; exact ⟨hpivot ▸ hxv, hx⟩
          · rintro (rfl | ⟨_, hx⟩)
            · exact hpivot ▸ hx_min_mem
            · exact hx
        -- f s = f ⟨cons (vertex n_min) rest _, _⟩ = color n_min = c_star
        have : f s = f ⟨Finset.cons (vertex n_min) rest hpivot_not,
            by rw [Finset.card_cons, hrest_card]⟩ := by
          congr 1; exact Subtype.ext hrecon
        rw [this, ← hpivot_color]
        convert hmono using 1
        exact Subtype.ext rfl
      · -- #H_final ≥ ℵ₀
        exact Cardinal.infinite_iff.mp (Set.infinite_coe_iff.mp hH_inf)

/-
## Section 5: Consequences and Consistency Checks
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

end Erdos1167
