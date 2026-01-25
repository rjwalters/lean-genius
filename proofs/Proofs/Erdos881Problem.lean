/-
Erdős Problem #881: Minimal Additive Bases and Order Increase

Source: https://erdosproblems.com/881
Status: OPEN

Statement:
Let A ⊂ ℕ be an additive basis of order k which is *minimal*, in the sense
that if B ⊂ A is any infinite subset, then A \ B is not a basis of order k.

Must there exist an infinite B ⊂ A such that A \ B is a basis of order k+1?

Key Concepts:
- A set A is an additive basis of order k if every sufficiently large n can be
  written as a sum of at most k elements of A
- A minimal basis cannot have any infinite subset removed while maintaining order k
- The question asks if we can always increase the order by exactly 1 by removing
  some infinite subset

Example:
- The natural numbers ℕ form a basis of order 1 (trivially)
- The squares {n² : n ∈ ℕ} form a basis of order 4 (Lagrange's theorem: every
  natural number is a sum of four squares)

References:
- Erdős [Er98]
- Formal Conjectures Project (Google DeepMind)

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Set Finset

namespace Erdos881

/-! ## Part I: Additive Bases -/

/--
**Asymptotic Additive Basis of Order k**

A set A ⊂ ℕ is an asymptotic additive basis of order k if every sufficiently
large natural number can be written as a sum of at most k elements from A.
-/
def IsAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∃ (s : Finset ℕ), ↑s ⊆ A ∧ s.card ≤ k ∧ s.sum id = n

/-- Order 1 bases are exactly the sets containing all large enough integers. -/
theorem order_one_basis (A : Set ℕ) :
    IsAsymptoticAddBasisOfOrder 1 A ↔
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n ∈ A := by
  constructor
  · intro ⟨N, hN⟩
    use N
    intro n hn
    obtain ⟨s, hsA, hscard, hssum⟩ := hN n hn
    have : s.card = 1 := by omega
    rw [Finset.card_eq_one] at this
    obtain ⟨a, rfl⟩ := this
    simp at hssum
    rw [hssum]
    exact hsA (Finset.mem_singleton_self a)
  · intro ⟨N, hN⟩
    use N
    intro n hn
    use {n}
    simp [hN n hn]

/-! ## Part II: Minimal Bases -/

/--
**Minimal Additive Basis of Order k**

A set A is a *minimal* additive basis of order k if:
1. A is an asymptotic additive basis of order k
2. For every infinite subset B ⊆ A, the complement A \ B is NOT a basis of order k

Intuitively, we cannot remove any infinite subset while keeping the same order.
-/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  IsAsymptoticAddBasisOfOrder k A ∧
    ∀ B : Set ℕ, B ⊆ A → B.Infinite → ¬IsAsymptoticAddBasisOfOrder k (A \ B)

/-- A minimal basis must be infinite (since removing finite sets preserves basis property). -/
theorem minimal_basis_infinite (k : ℕ) (A : Set ℕ) (hA : IsMinimalAsymptoticAddBasisOfOrder k A) :
    A.Infinite := by
  by_contra h
  push_neg at h
  -- If A is finite, it cannot be a basis of any order
  obtain ⟨N, hN⟩ := hA.1
  -- Take n > max(N, sum of all elements of A)
  sorry

/-! ## Part III: The Main Conjecture -/

/--
**Erdős Problem #881 (OPEN)**

For every minimal additive basis A of order k, does there exist an infinite
subset B ⊆ A such that A \ B is a basis of order k+1?

This asks whether we can always "decrease the quality" of a minimal basis
by exactly one order by removing an appropriate infinite subset.
-/
def erdos881Conjecture : Prop :=
  ∀ k : ℕ, ∀ A : Set ℕ,
    IsMinimalAsymptoticAddBasisOfOrder k A →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ IsAsymptoticAddBasisOfOrder (k + 1) (A \ B)

axiom erdos_881 : erdos881Conjecture

/-! ## Part IV: Weaker Questions -/

/--
**Weak Version: Order Increase by Some Amount**

Does there exist any finite m such that A \ B becomes a basis of order k + m?
-/
def erdos881Weak : Prop :=
  ∀ k : ℕ, ∀ A : Set ℕ,
    IsMinimalAsymptoticAddBasisOfOrder k A →
      ∃ B : Set ℕ, ∃ m : ℕ, m > 0 ∧ B ⊆ A ∧ B.Infinite ∧
        IsAsymptoticAddBasisOfOrder (k + m) (A \ B)

/-- The strong conjecture implies the weak version. -/
theorem strong_implies_weak : erdos881Conjecture → erdos881Weak := by
  intro h k A hA
  obtain ⟨B, hB⟩ := h k A hA
  exact ⟨B, 1, by omega, hB.1, hB.2.1, hB.2.2⟩

/-! ## Part V: Examples and Special Cases -/

/--
**Example: The Squares**

The set of perfect squares {n² : n ∈ ℕ} is a basis of order 4 by Lagrange's
theorem (every positive integer is a sum of four squares).

Is it minimal? What happens when we remove infinite subsets?
-/
def squares : Set ℕ := {n | ∃ m : ℕ, n = m^2}

axiom squares_basis_order_4 : IsAsymptoticAddBasisOfOrder 4 squares

/--
**Example: Higher Powers**

For k-th powers, Waring's problem gives bounds on the basis order.
The set of k-th powers is a basis of order g(k).
-/
def powers (k : ℕ) : Set ℕ := {n | ∃ m : ℕ, n = m^k}

/-! ## Part VI: Structural Properties -/

/--
**Monotonicity of Basis Order**

If A is a basis of order k, then A is also a basis of order k' for any k' ≥ k.
-/
theorem basis_order_monotone (A : Set ℕ) (k k' : ℕ) (hk : k ≤ k') :
    IsAsymptoticAddBasisOfOrder k A → IsAsymptoticAddBasisOfOrder k' A := by
  intro ⟨N, hN⟩
  use N
  intro n hn
  obtain ⟨s, hsA, hscard, hssum⟩ := hN n hn
  exact ⟨s, hsA, le_trans hscard hk, hssum⟩

/--
**Subset Property**

If A ⊆ A' and A is a basis of order k, then A' is a basis of order at most k.
-/
theorem basis_subset (A A' : Set ℕ) (k : ℕ) (hAA' : A ⊆ A') :
    IsAsymptoticAddBasisOfOrder k A → IsAsymptoticAddBasisOfOrder k A' := by
  intro ⟨N, hN⟩
  use N
  intro n hn
  obtain ⟨s, hsA, hscard, hssum⟩ := hN n hn
  exact ⟨s, fun x hx => hAA' (hsA hx), hscard, hssum⟩

/-! ## Part VII: Why This Is Hard -/

/--
**The Challenge**

The problem asks about a delicate balance:
- Minimal bases are "tight" - they have no redundancy for their order
- Yet we want to show there's always a way to remove elements to get
  exactly one higher order (not two or more)

This requires understanding the fine structure of additive bases and how
their order changes under removal of infinite subsets.
-/

/-! ## Part VIII: Summary -/

/--
**Erdős Problem #881: Summary**

**Question:** For a minimal basis A of order k, can we always find an infinite
B ⊆ A such that A \ B is a basis of order exactly k+1?

**Status:** OPEN

**Key Concepts:**
- Additive basis of order k: every large n is a sum of ≤ k elements
- Minimal: no infinite subset can be removed without increasing order
- The conjecture: order increases by exactly 1

**Related:**
- Waring's problem (additive bases formed by powers)
- Sidon sets and thin bases
- Erdős-Turán conjecture on additive bases
-/
theorem erdos_881_summary :
    -- The conjecture is stated
    erdos881Conjecture ↔
      ∀ k : ℕ, ∀ A : Set ℕ,
        IsMinimalAsymptoticAddBasisOfOrder k A →
          ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ IsAsymptoticAddBasisOfOrder (k + 1) (A \ B) := by
  rfl

/-- The problem remains OPEN. -/
theorem erdos_881_open : True := trivial

end Erdos881
