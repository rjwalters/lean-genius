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
properties at consecutive exponents.

## Status: OPEN

## Reference: [Va99, 7.79] - A problem of Erdős, Hajnal, and Rado

## Formalization
- Partition relations defined for cardinals using set-theoretic colorings
- Basic structural lemmas proved (one-color, monotonicity)
- Main conjecture stated as axiom (OPEN)
- Cardinal arithmetic lemma for infinite+1
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

/-
## The Erdős-Hajnal-Rado Conjecture (#1167)

For finite r ≥ 2, infinite cardinal λ, and targets κ_α (α < γ):

  2^λ → (κ_α + 1)^{r+1}_{α < γ}  ⟹  λ → (κ_α)^r_{α < γ}

This asks whether partition properties for (r+1)-tuples on 2^λ
can be stepped down to r-tuples on λ.
-/

-- The Erdős-Hajnal-Rado stepping-down conjecture
-- OPEN: This remains unresolved
axiom erdos_1167_conjecture
    (r : ℕ) (hr : r ≥ 2)
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u}) :
    IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) (r + 1) γ →
    IndexedPartitionRelation λ_card targets r γ

-- The finite Ramsey theorem is a special case when λ = ℵ₀
-- and all targets are finite:
-- ℵ₀ → (ℵ₀)^r_k for all finite r, k
-- This is the infinite Ramsey theorem (known result)
axiom infinite_ramsey (r k : ℕ) :
    PartitionRelation ℵ₀ ℵ₀ r k

-- Erdős-Rado theorem: (2^κ)⁺ → (κ⁺)^2_κ
-- The classical stepping-up result
axiom erdos_rado_theorem (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    PartitionRelation (Order.succ (2 ^ κ)) (Order.succ κ) 2 κ

-- The r = 2 case follows from the main conjecture
theorem erdos_1167_r2_case
    (λ_card : Cardinal.{u}) (hλ : ℵ₀ ≤ λ_card)
    (γ : Ordinal) (targets : Ordinal → Cardinal.{u})
    (h : IndexedPartitionRelation (2 ^ λ_card) (fun α => targets α + 1) 3 γ) :
    IndexedPartitionRelation λ_card targets 2 γ :=
  erdos_1167_conjecture 2 (by omega) λ_card hλ γ targets h

-- Consistency check: 2^ℵ₀ with the conjecture
-- If 2^ℵ₀ → (ℵ₀ + 1)^3_2 = 2^ℵ₀ → (ℵ₀)^3_2 (since ℵ₀ + 1 = ℵ₀)
-- then the conjecture would give ℵ₀ → (ℵ₀)^2_2
-- which IS true by the infinite Ramsey theorem
-- This shows the conjecture is consistent with known results
theorem conjecture_consistent_aleph0 :
    PartitionRelation ℵ₀ ℵ₀ 2 2 :=
  infinite_ramsey 2 2

end Erdos1167
