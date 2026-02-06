/-
Erdős Problem #881: Minimal Additive Bases and Order Increase

Let A ⊂ ℕ be an additive basis of order k which is minimal, in the sense
that if B ⊂ A is any infinite subset, then A \ B is not a basis of order k.

Must there exist an infinite B ⊂ A such that A \ B is a basis of order k+1?

**Status**: OPEN

Key Concepts:
- A set A is an additive basis of order k if every sufficiently large n can be
  written as a sum of at most k elements of A
- A minimal basis cannot have any infinite subset removed while maintaining order k
- The question asks if we can always increase the order by exactly 1 by removing
  some infinite subset

Example:
- The natural numbers ℕ form a basis of order 1 (trivially)
- The squares {n² : n ∈ ℕ} form a basis of order 4 (Lagrange's four-square theorem)

References:
- Erdős [Er98]
- https://erdosproblems.com/881
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Set Finset

namespace Erdos881

/- ## Part I: Additive Bases -/

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
    -- s.card ≤ 1 and s.sum id = n ≥ N; if s empty, sum = 0 ≠ n (when n ≥ N ≥ 0)
    -- But we need s nonempty to get card = 1
    have hne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h] at hssum
    have hcard1 : s.card = 1 := by have := hne.card_pos; omega
    rw [Finset.card_eq_one] at hcard1
    obtain ⟨a, rfl⟩ := hcard1
    simp only [Finset.sum_singleton, id] at hssum
    rw [← hssum]
    exact hsA (Finset.mem_coe.mpr (Finset.mem_singleton_self a))
  · intro ⟨N, hN⟩
    use N
    intro n hn
    exact ⟨{n}, by simp [hN n hn], by simp, by simp⟩

/- ## Part II: Minimal Bases -/

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

/-- A finite set cannot be an asymptotic additive basis of any order. -/
theorem finite_not_basis (k : ℕ) (A : Set ℕ) (hfin : A.Finite) :
    ¬IsAsymptoticAddBasisOfOrder k A := by
  intro ⟨N, hN⟩
  -- If A is finite (possibly empty), bound the max element
  by_cases hA_empty : A = ∅
  · -- A is empty: no finset s with ↑s ⊆ ∅ can have sum = N (unless N = 0 and s = ∅)
    obtain ⟨s, hsA, _, hssum⟩ := hN (N + 1) (by omega)
    have : s = ∅ := by
      by_contra hne
      rw [Finset.ne_empty_iff_nonempty] at hne
      obtain ⟨x, hx⟩ := hne
      exact (hA_empty ▸ hsA (Finset.mem_coe.mpr hx) : x ∈ (∅ : Set ℕ))
    simp [this] at hssum
  · -- A is nonempty and finite
    push_neg at hA_empty
    have hA_ne : hfin.toFinset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      apply hA_empty
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have := hfin.mem_toFinset.mpr hx
      rw [h] at this
      exact Finset.not_mem_empty _ this
    -- Let M be the maximum element of A
    let M := hfin.toFinset.max' hA_ne
    -- For any s ⊆ A with s.card ≤ k, s.sum id ≤ k * M
    have hbound : ∀ (s : Finset ℕ), ↑s ⊆ A → s.card ≤ k → s.sum id ≤ k * M := by
      intro s hsA hscard
      calc s.sum id = s.sum (fun x => x) := by simp [Function.comp_id]
        _ ≤ s.sum (fun _ => M) := by
            apply Finset.sum_le_sum
            intro x hx
            have hxA : x ∈ A := hsA (Finset.mem_coe.mpr hx)
            exact Finset.le_max' _ _ (hfin.mem_toFinset.mpr hxA)
        _ = s.card * M := by simp [Finset.sum_const, Algebra.id.smul_eq_mul]
        _ ≤ k * M := Nat.mul_le_mul_right M hscard
    -- Take n = max(N, k * M + 1): n ≥ N but s.sum id ≤ k * M < n
    obtain ⟨s, hsA, hscard, hssum⟩ := hN (max N (k * M + 1)) (le_max_left N _)
    have hle := hbound s hsA hscard
    omega

/-- A minimal basis must be infinite (since removing finite sets preserves basis property). -/
theorem minimal_basis_infinite (k : ℕ) (A : Set ℕ) (hA : IsMinimalAsymptoticAddBasisOfOrder k A) :
    A.Infinite := by
  by_contra h
  exact finite_not_basis k A (Set.not_infinite.mp h) hA.1

/- ## Part III: The Main Conjecture -/

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

/-- The conjecture is OPEN - axiomatized as it has no known proof or disproof. -/
axiom erdos_881 : erdos881Conjecture

/- ## Part IV: Weaker Questions -/

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

/- ## Part V: Examples and Special Cases -/

/--
**Example: The Squares**

The set of perfect squares {n² : n ∈ ℕ} is a basis of order 4 by Lagrange's
theorem (every positive integer is a sum of four squares).
-/
def squares : Set ℕ := {n | ∃ m : ℕ, n = m^2}

/-- Lagrange's four-square theorem implies squares are a basis of order 4. -/
axiom squares_basis_order_4 : IsAsymptoticAddBasisOfOrder 4 squares

/--
**Higher Powers and Waring's Problem**

For k-th powers, Waring's problem gives bounds on the basis order.
The set of k-th powers is a basis of order g(k).
-/
def powers (k : ℕ) : Set ℕ := {n | ∃ m : ℕ, n = m^k}

/- ## Part VI: Structural Properties -/

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

/- ## Part VII: Why This Is Hard -/

/--
**The Challenge**

The problem asks about a delicate balance:
- Minimal bases are "tight" - they have no redundancy for their order
- Yet we want to show there's always a way to remove elements to get
  exactly one higher order (not two or more)

This requires understanding the fine structure of additive bases and how
their order changes under removal of infinite subsets.
-/

/- ## Part VIII: Summary -/

/--
**Erdős Problem #881: Summary**

**Question:** For a minimal basis A of order k, can we always find an infinite
B ⊆ A such that A \ B is a basis of order exactly k+1?

**Status:** OPEN

**Key Results:**
- Additive basis of order k: every large n is a sum of ≤ k elements
- Minimal: no infinite subset can be removed without increasing order
- The conjecture: order increases by exactly 1
- Strong implies weak version (proved)
- Monotonicity and subset properties (proved)
-/
theorem erdos_881_summary :
    erdos881Conjecture ↔
      ∀ k : ℕ, ∀ A : Set ℕ,
        IsMinimalAsymptoticAddBasisOfOrder k A →
          ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ IsAsymptoticAddBasisOfOrder (k + 1) (A \ B) := by
  rfl

end Erdos881
