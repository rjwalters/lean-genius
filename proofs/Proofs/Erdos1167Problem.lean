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

/-
## Section 6: Proof of the Infinite Ramsey Theorem

Proved by induction on r with a "thinning chain" construction.
This theorem replaces the `infinite_ramsey` axiom above.

Proof outline (inductive step, r → r+1):
  Given f : [α]^{r+1} → β with α infinite (ℵ₀) and β finite (k colors):
  1. Build chain: pick x₀ ∈ α, restrict f to r-subsets fixing x₀,
     apply IH to get infinite monochromatic H₀ ⊆ α \ {x₀} with color c₀.
     Pick x₁ ∈ H₀, repeat. Produces sequences (xₙ), (cₙ), (Sₙ).
  2. Pigeonhole: cₙ ∈ β with β finite → some c* has infinite preimage I.
  3. A = {xₙ : n ∈ I} is infinite and monochromatic for f with color c*.
     Proof: any (r+1)-subset of A contains smallest element xₙ₀ (n₀ ∈ I),
     the rest is an r-subset of Sₙ₀₊₁ (monochromatic for f(· ∪ {xₙ₀}) = cₙ₀ = c*).

Once all sorries are resolved, the `infinite_ramsey` axiom can be removed,
reducing axiom count from 3 to 2.
-/

-- Helper: cardinality of an infinite subset of a type with #α = ℵ₀ is ℵ₀
private lemma mk_infinite_subset_eq_aleph0 {α : Type*}
    (hα : #α = ℵ₀) (S : Set α) (hS : Set.Infinite S) : #↥S = ℵ₀ := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le S).trans (le_of_eq hα)
  · by_contra h
    simp only [not_le] at h
    exact hS (Set.finite_coe_iff.mpr (Cardinal.lt_aleph0_iff_finite.mp h))

-- The infinite Ramsey theorem (proof by induction on r)
-- Once complete (all sorries resolved), this replaces the axiom `infinite_ramsey`
theorem infinite_ramsey_proved (r k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ r k := by
  induction r with
  | zero => exact infinite_ramsey_zero k
  | succ r ih =>
    intro α hα β hβ f
    classical
    -- α is infinite (cardinality ℵ₀)
    haveI hInfα : Infinite α := by
      by_contra h; simp only [not_infinite] at h
      exact absurd (Cardinal.lt_aleph0_iff_finite.mpr h)
        (not_lt.mpr (le_of_eq hα.symm))
    -- β is finite (cardinality k)
    haveI hFinβ : Finite β := Cardinal.lt_aleph0_iff_finite.mp
      (hβ ▸ Cardinal.nat_lt_aleph0 k)
    -- Handle vacuous case: β empty → no coloring can exist
    by_cases hβne : Nonempty β
    swap
    · -- β empty means k = 0, but RSubset α (r+1) is nonempty (α is infinite),
      -- so f : nonempty → empty is impossible
      have : Nonempty (RSubset α (r + 1)) := by
        -- An infinite type has finsets of any finite size
        -- Use Infinite.natEmbedding to get ℕ ↪ α, then map a range finset
        exact ⟨⟨(Finset.range (r + 1)).map (Infinite.natEmbedding α),
          by simp [Finset.card_map]⟩⟩
      exact absurd ⟨f this.some⟩ hβne
    -- ===== THINNING STEP =====
    -- For any infinite subset S ⊆ α, we can pick an element x ∈ S,
    -- apply the IH to the restricted coloring on S \ {x}, and get
    -- an infinite monochromatic subset T ⊆ S \ {x} with some color c.
    have thin_step : ∀ (S : Set α), Set.Infinite S →
        ∃ (x : α) (c : β) (T : Set α),
          x ∈ S ∧ Set.Infinite T ∧ T ⊆ S \ {x} ∧
          (∀ (s : Finset α) (_hs : s.card = r) (_hsub : (↑s : Set α) ⊆ T) (hxs : x ∉ s),
            f ⟨Finset.cons x s hxs, by rw [Finset.card_cons]; omega⟩ = c) := by
      intro S hS
      obtain ⟨x, hxS⟩ := hS.nonempty
      -- S \ {x} is infinite with cardinality ℵ₀
      have hS' : Set.Infinite (S \ {x}) := hS.diff (Set.finite_singleton x)
      have hcardS' : #↥(S \ {x}) = ℵ₀ := mk_infinite_subset_eq_aleph0 hα _ hS'
      -- Define restricted coloring g on r-subsets of (S \ {x}):
      -- g(T) = f({x} ∪ T), where T is lifted from the subtype to α
      let g : Coloring ↥(S \ {x}) r β := fun ⟨T, hcard⟩ =>
        let T' := T.map ⟨Subtype.val, Subtype.val_injective⟩
        have hx_nmem : x ∉ T' := by
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
          rintro ⟨⟨a, ha⟩, _, rfl⟩
          exact (Set.mem_diff_singleton.mp ha).2 rfl
        f ⟨Finset.cons x T' hx_nmem,
          by rw [Finset.card_cons, Finset.card_map, hcard]⟩
      -- Apply IH: PartitionRelation ℵ₀ ℵ₀ r k for the subtype ↥(S \ {x})
      obtain ⟨c, H, hMono, hHcard⟩ := ih ↥(S \ {x}) hcardS' β hβ g
      -- Convert H : Set ↥(S \ {x}) to T : Set α via Subtype.val
      refine ⟨x, c, Subtype.val '' H, hxS, ?_, ?_, ?_⟩
      · -- Subtype.val '' H is infinite (injective image of infinite set)
        have : Set.Infinite H := by
          rw [Set.infinite_coe_iff]
          by_contra hinf; simp only [not_infinite] at hinf
          exact absurd (Cardinal.lt_aleph0_iff_finite.mpr hinf)
            (not_lt.mpr hHcard)
        exact this.image Subtype.val_injective
      · -- Subtype.val '' H ⊆ S \ {x}
        exact Set.image_subset_iff.mpr fun ⟨a, ha⟩ _ => ha
      · -- Monochromaticity: for r-subsets s ⊆ (Subtype.val '' H) with x ∉ s,
        -- f(cons x s) = c
        -- Strategy: lift s to Finset ↥(S\{x}) via preimage, apply hMono, then
        -- connect back via T.map subtype_val = s
        intro s hs hsub hxs
        -- All elements of s are in S \ {x}
        have hs_diff : (↑s : Set α) ⊆ S \ {x} :=
          hsub.trans (Set.image_subset_iff.mpr fun ⟨_, ha⟩ _ => ha)
        -- Lift s to Finset of the subtype via preimage
        let T : Finset ↥(S \ {x}) :=
          s.preimage Subtype.val Subtype.val_injective.injOn
        -- T maps back to s
        have hT_map : T.map ⟨Subtype.val, Subtype.val_injective⟩ = s := by
          ext a; simp only [Finset.mem_map, Finset.mem_preimage,
            Function.Embedding.coeFn_mk]
          exact ⟨fun ⟨b, hb, rfl⟩ => hb,
            fun ha => ⟨⟨a, hs_diff (Finset.mem_coe.mpr ha)⟩, ha, rfl⟩⟩
        -- T has card r
        have hT_card : T.card = r := by
          rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, hT_map]; exact hs
        -- T ⊆ H (each element of T has its val in s ⊆ Subtype.val '' H)
        have hT_sub_H : (↑T : Set ↥(S \ {x})) ⊆ H := by
          intro b hb
          rw [Finset.mem_coe, Finset.mem_preimage] at hb
          obtain ⟨b', hb'H, hb'val⟩ := hsub (Finset.mem_coe.mpr hb)
          rwa [show b' = b from Subtype.val_injective hb'val] at hb'H
        -- Apply monochromaticity of g on H
        have hgc := hMono ⟨T, hT_card⟩ hT_sub_H
        -- hgc : g ⟨T, hT_card⟩ = c, which unfolds to
        -- f ⟨Finset.cons x (T.map subtype_val) _, _⟩ = c
        -- Since T.map subtype_val = s, this gives f ⟨Finset.cons x s _, _⟩ = c
        -- Definitional unfolding + rewrite to match goal
        change f ⟨Finset.cons x (T.map ⟨Subtype.val, Subtype.val_injective⟩) _ , _⟩ = c at hgc
        rw [hT_map] at hgc
        convert hgc using 2
        exact Subtype.ext rfl
    -- ===== CHAIN CONSTRUCTION =====
    -- Build decreasing chain of infinite sets using Nat.rec:
    --   state(0) = Set.univ (the whole of α, which is infinite)
    --   state(n+1) = T from thin_step applied to state(n)
    -- And extract element/color sequences from thin_step at each level.
    let state : ℕ → { S : Set α // Set.Infinite S } :=
      Nat.rec ⟨Set.univ, Set.infinite_univ⟩ fun _ ⟨S, hS⟩ =>
        let h := thin_step S hS
        ⟨h.choose_spec.choose_spec.choose,
         h.choose_spec.choose_spec.choose_spec.2.1⟩
    -- Element and color at step n (extracted from the same thin_step call)
    let getElem (n : ℕ) : α :=
      (thin_step (state n).val (state n).prop).choose
    let getColor (n : ℕ) : β :=
      (thin_step (state n).val (state n).prop).choose_spec.choose
    -- ===== KEY CHAIN PROPERTIES =====
    -- Property 1: getElem n ∈ (state n).val
    have hElem_in : ∀ n, getElem n ∈ (state n).val :=
      fun n => (thin_step (state n).val (state n).prop).choose_spec.choose_spec.choose_spec.1
    -- Property 2: state(n+1) ⊆ state(n) \ {getElem n}
    have hState_sub : ∀ n, (state (n + 1)).val ⊆ (state n).val \ {getElem n} :=
      fun n => (thin_step (state n).val (state n).prop).choose_spec.choose_spec.choose_spec.2.2.1
    -- Property 3: monochromaticity at each step
    have hStep_mono : ∀ n (s : Finset α) (_hs : s.card = r)
        (_hsub : (↑s : Set α) ⊆ (state (n + 1)).val) (hxs : getElem n ∉ s),
        f ⟨Finset.cons (getElem n) s hxs, by rw [Finset.card_cons]; omega⟩ = getColor n :=
      fun n => (thin_step (state n).val (state n).prop).choose_spec.choose_spec.choose_spec.2.2.2
    -- Monotonicity of state chain (without singleton removal)
    have hState_mono : ∀ n, (state (n + 1)).val ⊆ (state n).val :=
      fun n => (hState_sub n).trans Set.diff_subset
    -- Transitivity: state(m) ⊆ state(n) when n ≤ m
    have hState_mono_le : ∀ n m, n ≤ m → (state m).val ⊆ (state n).val := by
      intro n m hnm
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      induction d with
      | zero => exact Set.Subset.rfl
      | succ d ihd => exact (hState_mono (n + d)).trans ihd
    -- Property 4: for m > n, getElem m ∈ state(n+1)
    have hElem_in_later : ∀ n m, n < m → getElem m ∈ (state (n + 1)).val :=
      fun n m hnm => hState_mono_le (n + 1) m hnm (hElem_in m)
    -- getElem n ∉ state(n+1) (key for injectivity)
    have hElem_not_in_next : ∀ n, getElem n ∉ (state (n + 1)).val := by
      intro n hin
      have := hState_sub n hin
      exact (Set.mem_diff_singleton.mp this).2 rfl
    -- Property 5: getElem is injective
    have hElem_inj : Function.Injective getElem := by
      intro a b hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hElem_not_in_next a (hab ▸ hElem_in_later a b hlt)
      · exact hElem_not_in_next b (hab.symm ▸ hElem_in_later b a hlt)
    -- ===== PIGEONHOLE EXTRACTION =====
    -- getColor : ℕ → β with ℕ infinite and β finite
    -- By infinite pigeonhole, some color appears infinitely often
    obtain ⟨c_star, hc_star⟩ := Finite.exists_infinite_fiber getColor
    -- hc_star : Set.Infinite (getColor ⁻¹' {c_star})
    -- The monochromatic set: elements at indices where color = c*
    let A : Set α := getElem '' (getColor ⁻¹' {c_star})
    -- A is infinite (injective image of infinite set)
    have hA_inf : Set.Infinite A := hc_star.image hElem_inj.injOn
    -- ===== MONOCHROMATICITY VERIFICATION =====
    -- Any (r+1)-subset of A has color c* under f
    have hA_mono : IsMonochromatic f A c_star := by
      intro ⟨s, hcard⟩ hs
      -- For each a ∈ s, find its chain index (with color c* and getElem = a)
      have h_idx : ∀ a ∈ s, ∃ n, getColor n = c_star ∧ getElem n = a := by
        intro a ha
        obtain ⟨n, hn, rfl⟩ := hs (Finset.mem_coe.mpr ha)
        exact ⟨n, by rwa [Set.mem_preimage, Set.mem_singleton_iff] at hn, rfl⟩
      choose idx hidx using h_idx
      -- s is nonempty (r+1 ≥ 1)
      have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
      -- Build index set and find minimum index n₀
      let idx_of : { a // a ∈ s } → ℕ := fun ⟨a, ha⟩ => idx a ha
      let idx_set := s.attach.image idx_of
      have hne_idx : idx_set.Nonempty :=
        (Finset.attach_nonempty_iff.mpr hs_ne).image _
      let n₀ := idx_set.min' hne_idx
      -- n₀ is realized by some a₀ ∈ s with idx a₀ ha₀ = n₀
      have hn₀_mem : n₀ ∈ idx_set := Finset.min'_mem _ _
      rw [Finset.mem_image] at hn₀_mem
      obtain ⟨⟨a₀, ha₀⟩, _, hn₀_eq⟩ := hn₀_mem
      -- hn₀_eq : idx a₀ ha₀ = n₀
      have hn₀_elem : getElem n₀ = a₀ := by rw [← hn₀_eq]; exact (hidx a₀ ha₀).2
      have hn₀_color : getColor n₀ = c_star := by rw [← hn₀_eq]; exact (hidx a₀ ha₀).1
      -- Decompose s = cons a₀ (s.erase a₀)
      let rest := s.erase a₀
      have hrest_card : rest.card = r := by
        rw [Finset.card_erase_of_mem ha₀, hcard]; omega
      -- Every element of rest has index > n₀, so is in state(n₀+1)
      have hrest_sub : (↑rest : Set α) ⊆ (state (n₀ + 1)).val := by
        intro b hb_rest
        rw [Finset.mem_coe] at hb_rest
        have hbs : b ∈ s := Finset.erase_subset _ _ hb_rest
        have hbne : b ≠ a₀ := Finset.ne_of_mem_erase hb_rest
        -- n₀ ≤ idx b hbs (minimality)
        have hge : n₀ ≤ idx b hbs :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
        -- idx b hbs ≠ n₀ (since getElem injective and b ≠ a₀)
        have hne : idx b hbs ≠ n₀ := by
          intro h; apply hbne
          calc b = getElem (idx b hbs) := ((hidx b hbs).2).symm
            _ = getElem n₀ := by rw [h]
            _ = a₀ := hn₀_elem
        -- n₀ < idx b hbs
        rw [← (hidx b hbs).2]
        exact hElem_in_later n₀ _ (lt_of_le_of_ne hge hne)
      -- getElem n₀ ∉ rest (since getElem n₀ = a₀ and a₀ ∉ s.erase a₀)
      have hn₀_nrest : getElem n₀ ∉ rest := by rw [hn₀_elem]; exact Finset.not_mem_erase _ _
      -- Apply hStep_mono: f(cons (getElem n₀) rest) = getColor n₀ = c*
      have hstep := hStep_mono n₀ rest hrest_card hrest_sub hn₀_nrest
      rw [hn₀_color] at hstep
      -- Reconstruct: cons a₀ (s.erase a₀) = s
      have hrecons : Finset.cons a₀ rest (Finset.not_mem_erase _ _) = s :=
        Finset.cons_erase ha₀
      -- Goal: f ⟨s, hcard⟩ = c_star, known: f ⟨cons (getElem n₀) rest _, _⟩ = c_star
      -- These match since cons (getElem n₀) rest = cons a₀ rest = s
      convert hstep using 2
      apply Subtype.ext
      show s = Finset.cons (getElem n₀) rest hn₀_nrest
      rw [hn₀_elem]; exact hrecons.symm
    -- ===== CONCLUSION =====
    refine ⟨c_star, A, hA_mono, ?_⟩
    exact le_of_eq (mk_infinite_subset_eq_aleph0 hα A hA_inf).symm

end Erdos1167
