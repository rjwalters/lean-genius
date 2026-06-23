import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Abstract Group-Theoretic Product of Units Formula

## Overview

This file proves the key abstract group-theoretic theorem underlying Gauss's
generalization of Wilson's theorem:

> **Main Theorem**: In any finite commutative group G, if τ is the *unique*
> non-trivial involution (τ ≠ 1 and τ² = 1 with no other solutions), then
> the product of all elements of G equals τ.

**Cyclic Corollary**: Every finite cyclic group of even order has exactly one
non-trivial involution, so the product of all elements equals it.

This answers Wilson's Theorem OQ-04 Open Question 2: the abstract
group-theoretic lemma "∏G = τ for a unique involution τ" can indeed be
formalized cleanly and provides a more direct proof route.

## Main Results

- `prod_eq_prod_involutions` — involution pairing: ∏G = ∏{x | x² = 1}
- `card_sq_eq_one_le_two_cyclic` — in a finite cyclic group: |{x | x² = 1}| ≤ 2
- `prod_univ_of_unique_involution` — abstract product formula
- `IsCyclic.exists_unique_involution_of_even` — existence for cyclic groups
- `prod_cyclic_even_group` — combined result

## Proof Strategy

1. **Involution pairing**: In any finite abelian group, x ↦ x⁻¹ pairs
   non-self-inverse elements, so ∏G = ∏{x | x² = 1}.

2. **Cardinality bound**: `IsCyclic.card_pow_eq_one_le` gives |{x | x²=1}| ≤ 2
   in a cyclic group.

3. **Generator argument**: In an even-order cyclic group with generator g,
   τ = g^(|G|/2) satisfies τ² = 1 and τ ≠ 1, giving exactly 2 involutions.
-/

namespace WilsonsTheoremOQ04OQ02

open Finset

-- ============================================================================
-- Part 1: Involution Pairing Lemma (self-contained)
-- ============================================================================

/-- In a finite commutative group, the map x ↦ x⁻¹ pairs non-self-inverse
    elements. Consequence: ∏G = ∏{x ∈ G | x² = 1}.

    This key structural lemma says the product of a finite abelian group
    reduces to the product of its involutions (elements of order ≤ 2). -/
theorem prod_eq_prod_involutions (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ univ.filter (fun x : G => x ^ 2 = 1), x := by
  -- Split: ∏ G = ∏{x | x²=1} * ∏{x | x²≠1}
  have hsplit : ∏ x : G, x =
      (∏ x ∈ univ.filter (fun x : G => x ^ 2 = 1), x) *
      (∏ x ∈ univ.filter (fun x : G => ¬x ^ 2 = 1), x) :=
    (prod_filter_mul_prod_filter_not univ (fun x : G => x ^ 2 = 1) id).symm
  -- The second factor is 1: elements with x²≠1 pair under x↦x⁻¹
  have hrest : ∏ x ∈ univ.filter (fun x : G => ¬x ^ 2 = 1), x = 1 := by
    apply Finset.prod_involution (fun x _ => x⁻¹)
    · -- x * x⁻¹ = 1
      intros a _; exact mul_inv_cancel a
    · -- x ≠ x⁻¹ when x² ≠ 1
      intro a ha _
      simp only [mem_filter, mem_univ, true_and] at ha
      intro heq
      exact ha (by have h := mul_inv_cancel a; rw [heq] at h; rwa [← sq] at h)
    · -- Involution: (x⁻¹)⁻¹ = x  (Lean presents hg₄ before g_mem)
      intros a _; exact inv_inv a
    · -- x⁻¹ ∈ S when x ∈ S (x⁻¹ also has (x⁻¹)² ≠ 1)  (g_mem is goal 4)
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      simp only [mem_filter, mem_univ, true_and]
      rwa [inv_pow, inv_eq_one]
  rw [hsplit, hrest, mul_one]

-- ============================================================================
-- Part 2: Cardinality Bound for Cyclic Groups
-- ============================================================================

/-- In a finite cyclic group, the set of involutions {x | x² = 1} has
    at most 2 elements. This follows from IsCyclic.card_pow_eq_one_le. -/
theorem card_sq_eq_one_le_two_cyclic (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
    [IsCyclic G] :
    (univ.filter (fun x : G => x ^ 2 = 1)).card ≤ 2 :=
  IsCyclic.card_pow_eq_one_le (by norm_num : 0 < 2)

-- ============================================================================
-- Part 3: Abstract Product Formula
-- ============================================================================

/-- **Abstract Product Formula**: In a finite commutative group G, if τ is
    the unique non-trivial involution (τ ≠ 1, τ² = 1, and these are all
    solutions to x² = 1), then the product of all elements of G equals τ.

    This is the abstract group-theoretic core of the Gauss–Wilson theorem. -/
theorem prod_univ_of_unique_involution
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (τ : G) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (huniq : ∀ x : G, x ^ 2 = 1 → x = 1 ∨ x = τ) :
    ∏ x : G, x = τ := by
  -- ∏ G = ∏ {x | x² = 1}
  rw [prod_eq_prod_involutions G]
  -- {x | x² = 1} = {1, τ}
  have h_filter : univ.filter (fun x : G => x ^ 2 = 1) = {1, τ} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · exact huniq x
    · rintro (rfl | rfl)
      · exact one_pow 2
      · exact hτ2
  rw [h_filter]
  -- ∏ {1, τ} = 1 * τ = τ
  rw [Finset.prod_pair hτ1.symm]
  exact one_mul τ

-- ============================================================================
-- Part 4: Unique Involution Exists in Even-Order Cyclic Groups
-- ============================================================================

/-- In a finite cyclic group of even order, the half-generator g^(|G|/2) is
    the unique non-trivial involution.

    **Proof**: Let g be a generator with orderOf(g) = |G|. Set τ = g^(|G|/2).
    - τ² = g^|G| = 1 ✓
    - τ ≠ 1: if g^(|G|/2) = 1, then orderOf(g) ∣ |G|/2, giving |G| ∣ |G|/2,
      contradiction.
    - Uniqueness: |{x | x²=1}| ≤ 2 (cyclic), but {1, τ} has 2 elements, so
      {x | x²=1} = {1, τ}. -/
theorem IsCyclic.exists_unique_involution_of_even
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (h_even : Even (Fintype.card G)) :
    ∃ τ : G, τ ≠ 1 ∧ τ ^ 2 = 1 ∧ ∀ x : G, x ^ 2 = 1 → x = 1 ∨ x = τ := by
  -- Convert to Nat.card for orderOf lemmas
  have h_even_nat : Even (Nat.card G) := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ := h_even_nat  -- Nat.card G = k + k
  have hk_pos : 0 < k := by
    have := @Nat.card_pos G _ _; omega
  -- Pick generator g
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  -- Candidate: τ = g^k
  have hτ_ne : g ^ k ≠ 1 := by
    intro heq
    have hdvd := orderOf_dvd_of_pow_eq_one heq
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd hk_pos hdvd
    omega  -- hk: Nat.card G = k+k, hle: Nat.card G ≤ k  ⟹  k+k ≤ k, contradiction
  have hτ2 : (g ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = Nat.card G by omega, ← hord, pow_orderOf_eq_one]
  -- {1, g^k} ⊆ {x | x² = 1}
  have hsub : ({1, g ^ k} : Finset G) ⊆ univ.filter (fun x => x ^ 2 = 1) := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    simp only [mem_filter, mem_univ, true_and]
    rcases ha with rfl | rfl
    · exact one_pow 2
    · exact hτ2
  -- The filter equals {1, g^k} by cardinality squeeze
  have h_filter_eq : univ.filter (fun x : G => x ^ 2 = 1) = {1, g ^ k} := by
    apply (Finset.eq_of_subset_of_card_le hsub _).symm
    rw [Finset.card_pair hτ_ne.symm]
    exact card_sq_eq_one_le_two_cyclic G
  -- Conclude
  refine ⟨g ^ k, hτ_ne, hτ2, ?_⟩
  intro x hx
  have hx_mem : x ∈ univ.filter (fun y : G => y ^ 2 = 1) := by simp [hx]
  rw [h_filter_eq] at hx_mem
  simp only [mem_insert, mem_singleton] at hx_mem
  exact hx_mem

-- ============================================================================
-- Part 5: The Combined Cyclic Group Product Formula
-- ============================================================================

/-- **Cyclic Group Product Formula**: In a finite cyclic group of even order,
    the product of all elements equals the unique non-trivial involution.

    This is the abstract group-theoretic version of Gauss–Wilson: for the
    multiplicative group (ℤ/nℤ)× when it is cyclic and n ≥ 3, the product
    of all units equals -1 (the unique involution in (ℤ/nℤ)×).

    The result here is more general: it applies to any even-order cyclic group,
    without reference to modular arithmetic. -/
theorem prod_cyclic_even_group
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (h_even : Even (Fintype.card G)) :
    ∃ τ : G, τ ≠ 1 ∧ τ ^ 2 = 1 ∧ ∏ x : G, x = τ := by
  obtain ⟨τ, hτ_ne, hτ2, huniq⟩ :=
    IsCyclic.exists_unique_involution_of_even h_even
  exact ⟨τ, hτ_ne, hτ2, prod_univ_of_unique_involution τ hτ2 hτ_ne huniq⟩

-- ============================================================================
-- Part 6: Odd-Order Case
-- ============================================================================

/-- In a finite group of odd order, every element satisfies x² = 1 only if
    x = 1. Consequently, the product of all elements is 1.

    This is immediate: x² = 1 means x = x⁻¹, so orderOf(x) | 2. But |G| is
    odd, so orderOf(x) | gcd(2, |G|) = 1, i.e., x = 1. -/
theorem prod_univ_odd_order
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (h_odd : Odd (Fintype.card G)) :
    ∏ x : G, x = 1 := by
  -- In odd-order group, only x = 1 satisfies x² = 1
  have h_sq_one : ∀ x : G, x ^ 2 = 1 → x = 1 := by
    intro x hx
    have hord2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
    have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hord2
    have hpos : 0 < orderOf x := orderOf_pos x
    have hor : orderOf x = 1 ∨ orderOf x = 2 := by omega
    rcases hor with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hdvd : (2 : ℕ) ∣ Fintype.card G := h2 ▸ orderOf_dvd_card
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      rw [Nat.odd_iff] at h_odd
      omega
  -- ∏G = ∏{1} = 1
  rw [prod_eq_prod_involutions G]
  have h_filter : univ.filter (fun x : G => x ^ 2 = 1) = {1} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨h_sq_one x, fun hx => by rw [hx]; exact one_pow 2⟩
  rw [h_filter, Finset.prod_singleton]

end WilsonsTheoremOQ04OQ02
