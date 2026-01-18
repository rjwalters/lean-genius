/-
  Erdős Problem #817: Subset Sum Sets and Arithmetic Progressions

  **Problem**: Let k ≥ 3 and define g_k(n) to be the minimal N such that
  {1, ..., N} contains some A of size |A| = n such that

    ⟨A⟩ = {∑_{a∈A} ε_a·a : ε_a ∈ {0,1}}

  contains no non-trivial k-term arithmetic progression.
  Estimate g_k(n). In particular, is it true that g_3(n) ≫ 3^n?

  **Status**: OPEN (the main question g_3(n) ≫ 3^n is unresolved)

  **Known Results**:
  - Erdős and Sárközy proved g_3(n) ≫ 3^n / n^{O(1)}
  - This gives a lower bound up to polynomial factors
  - The conjecture asks whether the polynomial correction is necessary

  **Context**: This combines additive combinatorics (subset sums, arithmetic
  progressions) with extremal set theory. The subset sum set ⟨A⟩ has size
  at most 2^n, and the question asks how large N must be to find A ⊆ {1,...,N}
  whose subset sums avoid long arithmetic progressions.

  Reference: https://erdosproblems.com/817
  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib

open Finset Filter Nat

namespace Erdos817

/-
## Arithmetic Progressions

An arithmetic progression (AP) of length k is a sequence a, a+d, a+2d, ..., a+(k-1)d
where d > 0 is the common difference.
-/

/-- A set S contains no non-trivial k-term arithmetic progression if for all
    a, d with d > 0, at least one of a, a+d, ..., a+(k-1)d is not in S.

    A "trivial" AP would be one with d = 0 (constant sequence), which we exclude. -/
def IsAPFreeOfLength (k : ℕ) (S : Set ℕ) : Prop :=
  ∀ a d, d > 0 → ∃ i < k, a + i * d ∉ S

/-- Alternative definition: S is k-AP-free if no k-element subset forms an AP. -/
def IsAPFreeOfLength' (k : ℕ) (S : Set ℕ) : Prop :=
  ∀ a d, d > 0 → ¬∀ i < k, a + i * d ∈ S

/-- The two definitions are equivalent. -/
theorem apFree_iff (k : ℕ) (S : Set ℕ) :
    IsAPFreeOfLength k S ↔ IsAPFreeOfLength' k S := by
  simp only [IsAPFreeOfLength, IsAPFreeOfLength']
  constructor
  · intro h a d hd hAll
    obtain ⟨i, hi, hni⟩ := h a d hd
    exact hni (hAll i hi)
  · intro h a d hd
    by_contra hAll
    push_neg at hAll
    exact h a d hd hAll

/-
## Subset Sums

Given a finite set A of natural numbers, the subset sum set ⟨A⟩ consists
of all possible sums ∑_{a∈B} a where B ⊆ A.
-/

/-- The subset sum set: all sums of subsets of A. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun B => B.sum id)

/-- The empty sum is in subsetSums. -/
theorem zero_mem_subsetSums (A : Finset ℕ) : 0 ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  use ∅
  constructor
  · exact empty_subset A
  · simp

/-- The sum of all elements is in subsetSums. -/
theorem sum_mem_subsetSums (A : Finset ℕ) : A.sum id ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  exact ⟨A, Subset.refl A, rfl⟩

/-- Each element of A is in subsetSums. -/
theorem mem_subsetSums_of_mem (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    a ∈ subsetSums A := by
  simp only [subsetSums, mem_image, mem_powerset]
  use {a}
  simp [ha]

/-- The size of subsetSums is at most 2^|A|. -/
theorem card_subsetSums_le (A : Finset ℕ) : (subsetSums A).card ≤ 2^A.card := by
  calc (subsetSums A).card
      ≤ A.powerset.card := card_image_le
    _ = 2^A.card := card_powerset A

/-
## The Function g_k(n)

g_k(n) is the minimal N such that {1, ..., N} contains some A with |A| = n
where subsetSums(A) is k-AP-free.
-/

/-- A set A ⊆ {1, ..., N} of size n whose subset sums avoid k-term APs. -/
def ValidSet (k n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ A.card = n ∧
    IsAPFreeOfLength k (subsetSums A : Set ℕ)

/-- The set of all N for which a valid set exists. -/
def ValidNs (k n : ℕ) : Set ℕ := {N | ValidSet k n N}

/-- If N works, so does any larger N. -/
theorem validNs_upward_closed (k n N : ℕ) (hN : N ∈ ValidNs k n) (M : ℕ) (hM : N ≤ M) :
    M ∈ ValidNs k n := by
  obtain ⟨A, hA_sub, hA_card, hA_free⟩ := hN
  use A
  refine ⟨?_, hA_card, hA_free⟩
  exact hA_sub.trans (Icc_subset_Icc le_rfl hM)

/-- g_k(n) is the infimum of valid N values. For n ≥ 1, this is well-defined. -/
noncomputable def g (k n : ℕ) : ℕ := sInf (ValidNs k n)

/-
## The Main Conjecture (OPEN)

Erdős asked whether g_3(n) ≫ 3^n, i.e., whether there exists a constant c > 0
such that g_3(n) ≥ c · 3^n for all sufficiently large n.
-/

/-- **Erdős Problem #817 (OPEN)**: The main conjecture.

Is it true that g_3(n) ≫ 3^n? That is, does 3^n = O(g_3(n))?

This asks whether the subset sum set of any n-element subset of {1,...,N}
must contain a 3-term AP unless N is exponentially large in n. -/
def erdos817Conjecture : Prop :=
  (fun n => (3 ^ n : ℝ)) =O[atTop] fun n => (g 3 n : ℝ)

/-- Alternative formulation: there exists c > 0 such that g_3(n) ≥ c · 3^n
for all sufficiently large n. -/
def erdos817ConjectureAlt : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (g 3 n : ℝ) ≥ c * 3^n

/-
## The Erdős-Sárközy Partial Result

Erdős and Sárközy proved a weaker bound: g_3(n) ≫ 3^n / n^{O(1)}.
This is the polynomial-factor approximation to the full conjecture.
-/

/-- **Erdős-Sárközy Theorem**: g_3(n) ≫ 3^n / n^{O(1)}.

There exists a constant O > 0 such that 3^n / n^O = O(g_3(n)).
This is a partial result toward the main conjecture. -/
axiom erdosSarkozy_partial :
  ∃ O : ℝ, O > 0 ∧ (fun n : ℕ => (3 ^ n : ℝ) / (n : ℝ) ^ O) =O[atTop] fun n => (g 3 n : ℝ)

/-
## Basic Properties
-/

/-- The trivial lower bound: g_k(n) ≥ n since we need n distinct elements. -/
theorem g_ge_n (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 1) : g k n ≥ n := by
  -- Any A ⊆ {1,...,N} with |A| = n requires N ≥ n
  sorry

/-- An upper bound: g_3(n) ≤ 3^n (trivially, using {1, 3, 9, ..., 3^(n-1)}). -/
theorem g3_le_exp (n : ℕ) (hn : n ≥ 1) : g 3 n ≤ 3^n := by
  -- The set {1, 3, 9, ..., 3^(n-1)} works
  -- Its subset sums are all numbers in base 3 with digits 0 or 1
  -- This is a Sidon-like set avoiding 3-APs
  sorry

/-
## Examples for Small Cases
-/

/-- For n = 1: g_3(1) = 1 since A = {1} has subset sums {0, 1}, which is 3-AP-free. -/
theorem g3_one : g 3 1 = 1 := by
  -- The set {1} has subset sums {0, 1}
  -- No 3-term AP can fit in {0, 1}
  sorry

/-- For n = 2: g_3(2) = 2 since A = {1, 2} has subset sums {0, 1, 2, 3}, which
    contains the 3-AP (0, 1, 2) if d = 1. But A = {1, 3} has sums {0, 1, 3, 4},
    which is 3-AP-free. -/
theorem g3_two : g 3 2 = 2 := by
  -- Need to show 2 is the minimum N
  sorry

/-
## Heuristic Analysis

Why should g_3(n) be exponential in n?

1. The subset sum set ⟨A⟩ has at most 2^n elements (all subsets)
2. A random subset of {1, ..., N} of density ρ contains a 3-AP with high
   probability when ρ > c·N^{-1/2} (Szemerédi/Roth)
3. So ⟨A⟩ of size 2^n should avoid 3-APs only if 2^n / max(⟨A⟩) is small
4. If A ⊆ {1, ..., N}, then max(⟨A⟩) ≤ n·N
5. To have 2^n / (n·N) small, we need N exponential in n
-/

/-- The maximum element in subsetSums is bounded by n times the max of A. -/
theorem max_subsetSums_le (A : Finset ℕ) (N : ℕ) (hAN : ∀ a ∈ A, a ≤ N) :
    ∀ s ∈ subsetSums A, s ≤ A.card * N := by
  intro s hs
  simp only [subsetSums, mem_image, mem_powerset] at hs
  obtain ⟨B, hB_sub, rfl⟩ := hs
  calc B.sum id
      ≤ B.card * N := by
        apply Finset.sum_le_card_nsmul
        intro x hx
        exact hAN x (hB_sub hx)
    _ ≤ A.card * N := by
        apply Nat.mul_le_mul_right
        exact card_le_card hB_sub

/-
## Connection to Szemerédi's Theorem

Szemerédi's theorem (1975) says: any subset of {1, ..., N} of size δN
contains a k-term arithmetic progression for N large enough (depending on δ, k).

This implies that avoiding 3-APs requires sparse sets. The question is:
how sparse must ⟨A⟩ be, and how does this constrain A?
-/

/-- Szemerédi's theorem (axiom): dense sets contain long arithmetic progressions. -/
axiom szemeredi_theorem :
  ∀ k ≥ 3, ∀ δ : ℝ, δ > 0 → ∃ N₀, ∀ N ≥ N₀, ∀ S : Finset ℕ, S ⊆ Icc 1 N →
    S.card ≥ δ * N → ¬IsAPFreeOfLength k (S : Set ℕ)

end Erdos817
