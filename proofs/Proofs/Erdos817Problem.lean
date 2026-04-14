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
/-
## Basic Properties
-/

/-- The trivial lower bound: g_k(n) ≥ n since we need n distinct elements.

  Key insight: any A ⊆ {1,...,N} with |A| = n has A.card ≤ |{1,...,N}| = N, so N ≥ n.
  The lower bound g_k(n) ≥ n follows since every N in ValidNs k n satisfies N ≥ n.
  The nonemptiness of ValidNs k n requires an explicit AP-free construction. -/
theorem g_ge_n (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 1) : g k n ≥ n := by
  apply le_csInf
  · -- Nonemptiness: need to exhibit some valid N (hard — requires AP-free construction)
    -- The set {1, k, k^2, ..., k^{n-1}} ⊆ {1,...,k^n} works but AP-freeness is non-trivial
    sorry
  · -- Lower bound: every valid N satisfies N ≥ n
    -- Because A ⊆ {1,...,N} with |A| = n implies |A| ≤ |{1,...,N}| = N
    intro N ⟨A, hAsub, hAcard, _⟩
    have hcard : A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hAsub
    rw [Nat.card_Icc] at hcard
    omega

/-- An upper bound: g_3(n) ≤ 3^n (trivially, using {1, 3, 9, ..., 3^(n-1)}). -/
theorem g3_le_exp (n : ℕ) (hn : n ≥ 1) : g 3 n ≤ 3^n := by
  -- The set {1, 3, 9, ..., 3^(n-1)} works
  -- Its subset sums are all numbers in base 3 with digits 0 or 1
  -- This is a Sidon-like set avoiding 3-APs
  sorry

/-
## Examples for Small Cases
-/

/-- For n = 1: g_3(1) = 1 since A = {1} has subset sums {0, 1}, which is 3-AP-free.

  Proof: Upper bound — A = {1} ⊆ {1,...,1} with |A| = 1 and subsetSums = {0,1}
  is 3-AP-free (any AP a,a+d,a+2d with d≥1 has a+2d ≥ 2 > 1, so it leaves {0,1}).
  Lower bound — any A ⊆ {1,...,N} with |A| = 1 has an element a ≥ 1, so N ≥ 1. -/
theorem g3_one : g 3 1 = 1 := by
  -- Decidable computation: subsetSums {1} = {0, 1} as Finsets
  have hss1 : subsetSums ({1} : Finset ℕ) = ({0, 1} : Finset ℕ) := by native_decide
  -- AP-freeness: subsetSums {1} = {0,1} has no 3-AP (for any a,d>0: a+2d ≥ 2 ∉ {0,1})
  have hfree1 : IsAPFreeOfLength 3 (subsetSums ({1} : Finset ℕ) : Set ℕ) := by
    simp only [hss1, Finset.coe_insert, Finset.coe_singleton]
    intro a d hd
    exact ⟨2, by norm_num, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega⟩
  -- 1 ∈ ValidNs 3 1 via A = {1} ⊆ Icc 1 1
  have h1mem : (1 : ℕ) ∈ ValidNs 3 1 :=
    ⟨{1}, by simp [Finset.subset_iff, Finset.mem_Icc], rfl, hfree1⟩
  apply Nat.le_antisymm
  · exact Nat.sInf_le h1mem
  · -- Lower bound: any A ⊆ {1,...,N} with |A|=1 has an element a≥1, so N≥1
    apply le_csInf ⟨1, h1mem⟩
    intro N ⟨A, hAsub, hAcard, _⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hAcard
    exact (Finset.mem_Icc.mp (hAsub (Finset.mem_singleton_self a))).1

/-- For n = 2: g_3(2) = 3.

  Note: the original claim g_3(2) = 2 was incorrect.
  - N = 0, 1: no 2-element subset of {1,...,N} exists.
  - N = 2: only choice is A = {1,2}, but subsetSums {1,2} = {0,1,2,3} contains the
    3-AP (0,1,2) with d=1.
  - N = 3: A = {1,3} ⊆ {1,...,3} has subsetSums = {0,1,3,4}, which is 3-AP-free.
    Proof: if a, a+d ∈ {0,1,3,4} with d > 0, then a+2d ∉ {0,1,3,4} (omega). -/
theorem g3_two : g 3 2 = 3 := by
  -- Decidable Finset computations
  have hss13 : subsetSums ({1, 3} : Finset ℕ) = ({0, 1, 3, 4} : Finset ℕ) := by native_decide
  have hss12 : subsetSums ({1, 2} : Finset ℕ) = ({0, 1, 2, 3} : Finset ℕ) := by native_decide
  -- AP-freeness: {1,3}'s subset sums (={0,1,3,4}) contain no 3-AP
  -- Key: if a, a+d ∈ {0,1,3,4} with d>0, then a+2d ∉ {0,1,3,4} (verified by omega)
  have hfree13 : IsAPFreeOfLength 3 (subsetSums ({1, 3} : Finset ℕ) : Set ℕ) := by
    simp only [hss13, Finset.coe_insert, Finset.coe_singleton]
    intro a d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h0 : a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 4
    · by_cases h1 : a + d = 0 ∨ a + d = 1 ∨ a + d = 3 ∨ a + d = 4
      · exact ⟨2, by norm_num, by omega⟩  -- a, a+d ∈ {0,1,3,4} ⟹ a+2d ∉ {0,1,3,4}
      · push_neg at h1; exact ⟨1, by norm_num, by omega⟩
    · push_neg at h0; exact ⟨0, by norm_num, by simpa using h0⟩
  -- 3 ∈ ValidNs 3 2 via A = {1,3} ⊆ Icc 1 3 with |A|=2 and AP-free sums
  have h3mem : (3 : ℕ) ∈ ValidNs 3 2 := by
    refine ⟨{1, 3}, ?_, by native_decide, hfree13⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  -- 2 ∉ ValidNs 3 2: subsetSums {1,2} = {0,1,2,3} contains the 3-AP 0,1,2
  have h2nmem : (2 : ℕ) ∉ ValidNs 3 2 := by
    intro ⟨A, hAsub, hAcard, hAfree⟩
    -- Force A = {1,2} (only 2-element subset of Icc 1 2)
    have hIcc2 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by native_decide
    rw [hIcc2] at hAsub
    have hA12 : A = {1, 2} :=
      Finset.eq_of_subset_of_card_le hAsub (by
        have : ({1, 2} : Finset ℕ).card = 2 := by native_decide
        omega)
    subst hA12
    -- The AP 0, 1, 2 with d=1 lies entirely in subsetSums {1,2} = {0,1,2,3}
    obtain ⟨i, hi, hmem⟩ := hAfree 0 1 (by norm_num)
    simp only [Finset.mem_coe] at hmem
    rw [hss12] at hmem
    simp only [zero_add, mul_one, Finset.mem_insert, Finset.mem_singleton] at hmem
    omega  -- i < 3 forces i ∈ {0,1,2}, but all are in {0,1,2,3} — contradiction
  apply Nat.le_antisymm
  · exact Nat.sInf_le h3mem
  · apply le_csInf ⟨3, h3mem⟩
    intro N hN
    by_contra hlt; push_neg at hlt
    interval_cases N
    · obtain ⟨A, hAsub, hAcard, _⟩ := hN  -- N = 0
      have : A.card ≤ (Finset.Icc 1 0).card := Finset.card_le_card hAsub
      simp at this; omega
    · obtain ⟨A, hAsub, hAcard, _⟩ := hN  -- N = 1
      have : A.card ≤ (Finset.Icc 1 1).card := Finset.card_le_card hAsub
      simp at this; omega
    · exact h2nmem hN  -- N = 2: use h2nmem

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
end Erdos817
