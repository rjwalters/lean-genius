/-
Erdős Problem #881: Minimal Additive Bases and Order Increase

Let A ⊂ ℕ be an additive basis of order k which is minimal, in the sense
that if B ⊂ A is any infinite subset, then A \ B is not a basis of order k.

Must there exist an infinite B ⊂ A such that A \ B is a basis of order k+1?

**Status**: OPEN

Key Concepts:
- A set A is an additive basis of order k if every sufficiently large n can be
  written as a sum of at most k elements of A (with repetition)
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

import Mathlib

open Set

namespace Erdos881

/- ## Part I: Additive Bases -/

/--
**Asymptotic Additive Basis of Order k**

A set A ⊂ ℕ is an asymptotic additive basis of order k if every sufficiently
large natural number can be written as a sum of at most k elements from A
(with repetition allowed, using Multiset).
-/
def IsAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ (s : Multiset ℕ), (∀ a ∈ s, a ∈ A) ∧ Multiset.card s ≤ k ∧ s.sum = n

/-- Order 1 bases are exactly the sets containing all large enough integers. -/
theorem order_one_basis (A : Set ℕ) :
    IsAsymptoticAddBasisOfOrder 1 A ↔
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n ∈ A := by
  constructor
  · intro ⟨N, hN⟩
    -- Use max N 1 to ensure n ≥ 1, so the multiset can't be empty
    use max N 1
    intro n hn
    have hn_N : n ≥ N := le_trans (le_max_left N 1) hn
    have hn_pos : n ≥ 1 := le_trans (le_max_right N 1) hn
    obtain ⟨s, hsA, hscard, hssum⟩ := hN n hn_N
    have hne : s ≠ 0 := by
      intro h; simp [h] at hssum; omega
    have hpos : 0 < Multiset.card s := Multiset.card_pos.mpr hne
    have hcard1 : Multiset.card s = 1 := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hcard1
    simp at hssum
    rw [← hssum]
    exact hsA a (Multiset.mem_singleton_self a)
  · intro ⟨N, hN⟩
    use N
    intro n hn
    refine ⟨{n}, ?_, by simp, by simp⟩
    intro a ha
    simp at ha
    rw [ha]; exact hN n hn

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
  by_cases hne : A.Nonempty
  · -- A is nonempty and finite: any multiset with elements from A has bounded sum
    have hfin_ne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
    let M := hfin.toFinset.max' hfin_ne
    have hbound : ∀ (s : Multiset ℕ), (∀ a ∈ s, a ∈ A) → Multiset.card s ≤ k →
        s.sum ≤ k * M := by
      intro s hsA hscard
      calc s.sum ≤ Multiset.card s • M :=
              Multiset.sum_le_card_nsmul s M (fun x hx =>
                Finset.le_max' _ _ (hfin.mem_toFinset.mpr (hsA x hx)))
        _ = Multiset.card s * M := by ring
        _ ≤ k * M := Nat.mul_le_mul_right M hscard
    obtain ⟨s, hsA, hscard, hssum⟩ := hN (max N (k * M + 1)) (le_max_left N _)
    have hle := hbound s hsA hscard
    omega
  · -- A is empty: any valid multiset must be empty
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨s, hsA, _, hssum⟩ := hN (N + 1) (by omega)
    have : s = 0 := Multiset.eq_zero_of_forall_notMem
      (fun a ha => absurd (hsA a ha) (hne ▸ Set.notMem_empty a))
    simp [this] at hssum

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
def squares : Set ℕ := {n | ∃ m : ℕ, n = m ^ 2}

/-- Lagrange's four-square theorem implies squares are a basis of order 4.
    Proved from Mathlib's `Nat.sum_four_squares`. -/
theorem squares_basis_order_4 : IsAsymptoticAddBasisOfOrder 4 squares := by
  use 0
  intro n _
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨↑[a ^ 2, b ^ 2, c ^ 2, d ^ 2], ?_, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp
  · simp [Multiset.sum_coe]; omega

/--
**Higher Powers and Waring's Problem**

For k-th powers, Waring's problem gives bounds on the basis order.
The set of k-th powers is a basis of order g(k).
-/
def powers (k : ℕ) : Set ℕ := {n | ∃ m : ℕ, n = m ^ k}

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
  exact ⟨s, fun x hx => hAA' (hsA x hx), hscard, hssum⟩

/- ## Part VII: Summary -/

/--
**Erdős Problem #881: Summary**

**Question:** For a minimal basis A of order k, can we always find an infinite
B ⊆ A such that A \ B is a basis of order exactly k+1?

**Status:** OPEN

**Key Results:**
- Additive basis of order k: every large n is a sum of ≤ k elements (with repetition)
- Minimal: no infinite subset can be removed without increasing order
- The conjecture: order increases by exactly 1
- Strong implies weak version (proved)
- Monotonicity and subset properties (proved)
- Squares are a basis of order 4 (proved from Lagrange via Mathlib)
-/
theorem erdos_881_summary :
    erdos881Conjecture ↔
      ∀ k : ℕ, ∀ A : Set ℕ,
        IsMinimalAsymptoticAddBasisOfOrder k A →
          ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ IsAsymptoticAddBasisOfOrder (k + 1) (A \ B) := by
  rfl

end Erdos881
