/-
Erdős Problem #348

For what values of 0 ≤ m < n is there a complete sequence A = {a₁ ≤ a₂ ≤ ...}
of integers such that:
1. A remains complete after removing any m elements, but
2. A is not complete after removing any n elements.

A sequence is complete if every sufficiently large integer can be represented
as a sum of distinct elements from the sequence.

The problem was posed by Erdős and Graham [ErGr80]. Known cases include:
- (m=0, n=1): Powers of 2 work - the sequence is complete but removing any
  element breaks completeness.
- (m=1, n=2): The Fibonacci sequence works - it remains complete after removing
  one element, but removing two can break it.

The case (m=2, n=3) remains open.

Reference: https://erdosproblems.com/348
-/

import Mathlib

namespace Erdos348

/-
## Complete Sequences

A sequence A of positive integers is complete if every sufficiently large
positive integer can be written as a sum of distinct elements of A.
-/

/-- The set of all finite sums of distinct elements from a set -/
def finiteSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, ↑S ⊆ A ∧ n = S.sum id}

/-- A set is complete if it represents all sufficiently large integers -/
def IsComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, n ∈ finiteSums A

/-- Alternative: complete means represents all natural numbers -/
def IsStronglyComplete (A : Set ℕ) : Prop :=
  ∀ n : ℕ, n ∈ finiteSums A

/-- A sequence viewed as a set -/
def sequenceToSet (a : ℕ → ℕ) : Set ℕ := Set.range a

/-
## Removing Elements

We need to formalize what it means to remove elements from a sequence.
-/

/-- Remove a finite set of indices from a sequence -/
noncomputable def removeIndices (a : ℕ → ℕ) (S : Finset ℕ) : Set ℕ :=
  {a i | i ∉ S}

/-- Alternative: remove by values instead of indices -/
def removeValues (A : Set ℕ) (S : Finset ℕ) : Set ℕ :=
  A \ ↑S

/-
## The Main Problem Statement

For given m < n, does there exist a complete sequence that:
- Remains complete after removing any m elements
- Becomes incomplete after removing some n elements
-/

/-- A sequence is m-robust if it stays complete after removing any m indices -/
def IsRobust (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → IsComplete (removeIndices a S)

/-- A sequence is not n-robust if removing some n indices breaks completeness -/
def NotRobust (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = n ∧ ¬IsComplete (removeIndices a S)

/-- The set of valid (m, n) pairs for the problem -/
def validPairs : Set (ℕ × ℕ) :=
  {p | p.1 < p.2 ∧
       ∃ a : ℕ → ℕ, Monotone a ∧ IsComplete (sequenceToSet a) ∧
         IsRobust a p.1 ∧ NotRobust a p.2}

/-
## Known Examples

The powers of 2 show (0, 1) is valid.
The Fibonacci sequence shows (1, 2) is valid.
-/

/-- Powers of 2: 1, 2, 4, 8, ... -/
def powersOf2 (n : ℕ) : ℕ := 2^n

/-- The Fibonacci sequence: 1, 2, 3, 5, 8, 13, ... -/
def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => fib n + fib (n + 1)

/-- Every natural number is a sum of distinct powers of 2 (binary representation). -/
private lemma binary_sum : ∀ n : ℕ, ∃ S : Finset ℕ, (∀ x ∈ S, ∃ k : ℕ, x = 2 ^ k) ∧ n = S.sum id := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact ⟨∅, fun _ h => absurd h (Finset.not_mem_empty _), by simp⟩
    | n + 1 =>
      -- Let k = Nat.log 2 (n+1), giving 2^k ≤ n+1 < 2^(k+1)
      set k := Nat.log 2 (n + 1) with hk_def
      have hk_le : 2 ^ k ≤ n + 1 := Nat.pow_log_le_self 2 (n + 1)
      have hk_lt : n + 1 < 2 ^ (k + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 1)
      -- m = n + 1 - 2^k < n + 1
      set m := n + 1 - 2 ^ k with hm_def
      have hm_lt : m < n + 1 := Nat.sub_lt (by omega) (by positivity)
      obtain ⟨S', hS'_pow, hS'_sum⟩ := ih m hm_lt
      -- Claim: 2^k ∉ S' (each element ≤ sum = m < 2^k)
      have h2k_notin : (2 : ℕ) ^ k ∉ S' := by
        intro hmem
        have hle := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem
        simp only [id] at hle
        -- hle : 2^k ≤ S'.sum id, hS'_sum : m = S'.sum id, hk_lt : n+1 < 2^(k+1)
        rw [pow_succ] at hk_lt
        omega
      -- Build S = insert (2^k) S'
      refine ⟨Finset.cons (2 ^ k) S' h2k_notin, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨k, rfl⟩
        · exact hS'_pow x hx
      · simp only [Finset.sum_cons, id]
        omega

/-- Powers of 2 are complete (binary representation exists). -/
theorem powersOf2_complete : IsComplete (sequenceToSet powersOf2) := by
  use 0
  intro n _
  obtain ⟨S, hS_pow, hS_sum⟩ := binary_sum n
  refine ⟨S, ?_, hS_sum⟩
  intro x hx
  obtain ⟨k, rfl⟩ := hS_pow x (Finset.mem_coe.mp hx)
  exact Set.mem_range.mpr ⟨k, rfl⟩

/-- Powers of 2 are not 1-robust: removing 2^0=1 breaks completeness.
    Every remaining element is even, so all sums are even, but odd numbers exist. -/
theorem powersOf2_not_1_robust : NotRobust powersOf2 1 := by
  use {0}
  refine ⟨Finset.card_singleton 0, ?_⟩
  intro ⟨N, hN⟩
  -- The number 2*N+1 ≥ N should be representable
  have h := hN (2 * N + 1) (by omega)
  simp only [finiteSums, Set.mem_setOf_eq] at h
  obtain ⟨T, hT_sub, hT_sum⟩ := h
  -- Every element of T is a power of 2 with exponent ≥ 1, hence even
  have heven : 2 ∣ T.sum id := by
    apply Finset.dvd_sum
    intro x hx
    have hmem : x ∈ removeIndices powersOf2 {0} := hT_sub (Finset.mem_coe.mpr hx)
    simp only [removeIndices, Set.mem_setOf_eq, Finset.mem_singleton] at hmem
    obtain ⟨i, hi_ne, hi_eq⟩ := hmem
    simp only [powersOf2] at hi_eq; rw [hi_eq]
    exact dvd_pow_self 2 hi_ne
  -- But 2*N+1 is odd — contradiction
  rw [hT_sum] at heven
  omega

/-- (0, 1) is a valid pair -/
theorem pair_0_1_valid : (0, 1) ∈ validPairs := by
  constructor
  · norm_num
  · use powersOf2
    constructor
    · intro m n hmn
      simp [powersOf2]
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hmn
    constructor
    · exact powersOf2_complete
    constructor
    · -- 0-robustness is trivial (nothing removed)
      intro S hS
      rw [Finset.card_eq_zero] at hS
      simp [hS, removeIndices]
      exact powersOf2_complete
    · exact powersOf2_not_1_robust

/-- Fibonacci sequence is 1-robust: removing one element doesn't break completeness.
    Deep result about the redundancy structure of Fibonacci representations. -/
axiom fib_1_robust : IsRobust fib 1

/-- Fibonacci is monotone at each step. -/
private lemma fib_mono_succ (n : ℕ) : fib n ≤ fib (n + 1) := by
  cases n with
  | zero => show (1 : ℕ) ≤ 2; omega
  | succ k => show fib (k + 1) ≤ fib k + fib (k + 1); omega

/-- Fibonacci is strictly monotone. -/
private lemma fib_strictMono : StrictMono fib := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => show (1 : ℕ) < 2; omega
  | succ k =>
    show fib (k + 1) < fib k + fib (k + 1)
    have : 0 < fib k := by cases k <;> simp [fib]; omega
    omega

/-- fib(k) ≥ k + 1 for k ≥ 1 (fib grows faster than linear). -/
private lemma fib_ge_succ : ∀ k, 1 ≤ k → k + 1 ≤ fib k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    match k with
    | 0 => omega
    | 1 => simp [fib]
    | 2 => simp [fib]
    | k + 3 =>
      simp [fib]
      have := ih (k + 1) (by omega) (by omega)
      have := ih (k + 2) (by omega) (by omega)
      omega

/-- fib(k+1) ≤ 2 * fib(k) for all k: the next Fibonacci is at most double. -/
private lemma fib_succ_le_double (k : ℕ) : fib (k + 1) ≤ 2 * fib k := by
  match k with
  | 0 => show (2 : ℕ) ≤ 2 * 1; omega
  | k + 1 =>
    show fib k + fib (k + 1) ≤ 2 * fib (k + 1)
    have := fib_mono_succ k; omega

/-- For any n ≥ 1, find the largest Fibonacci index k with fib k ≤ n. -/
private lemma fib_bracketing (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, fib k ≤ n ∧ n < fib (k + 1) := by
  have ⟨j, hj⟩ : ∃ j, n < fib j :=
    ⟨n + 1, lt_of_lt_of_le (by omega) (fib_ge_succ (n + 1) (by omega))⟩
  set j₀ := Nat.find ⟨j, hj⟩ with hj₀_def
  have hmin : n < fib j₀ := Nat.find_spec ⟨j, hj⟩
  have hj₀_pos : 1 ≤ j₀ := by
    by_contra h; push_neg at h
    have : j₀ = 0 := by omega
    rw [this, fib] at hmin; omega
  have hprev : ¬(n < fib (j₀ - 1)) := Nat.find_min ⟨j, hj⟩ (by omega)
  exact ⟨j₀ - 1, by omega, by rwa [show j₀ - 1 + 1 = j₀ from by omega]⟩

/-- Fibonacci sequence is complete: every natural number is a sum of distinct
    Fibonacci values. Proof by greedy algorithm: take the largest fib(k) ≤ n,
    then n - fib(k) < fib(k) (since fib(k+1) ≤ 2·fib(k)), so the IH applies.
    fib(k) exceeds any element of the representing set for n-fib(k), so fib(k)
    is fresh and can be inserted. -/
theorem fib_complete : IsComplete (sequenceToSet fib) := by
  use 0
  suffices h : ∀ n, n ∈ finiteSums (sequenceToSet fib) by exact fun n _ => h n
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact ⟨∅, Set.empty_subset _, by simp⟩
    | n + 1 =>
      obtain ⟨k, hk_le, hk_lt⟩ := fib_bracketing (n + 1) (by omega)
      have hlt_fib : n + 1 - fib k < fib k := by
        have := fib_succ_le_double k; omega
      obtain ⟨S, hS_sub, hS_sum⟩ := ih (n + 1 - fib k) (by omega)
      have hfk_notin : fib k ∉ S := by
        intro hmem
        have : fib k ≤ S.sum id :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
        omega
      refine ⟨insert (fib k) S, ?_, ?_⟩
      · intro x hx
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Set.mem_range.mpr ⟨k, rfl⟩
        · exact hS_sub (Finset.mem_coe.mpr hx)
      · rw [Finset.sum_insert hfk_notin]; simp only [id]; omega

/-- fib(i) ≥ 3 for i ≥ 2. -/
private lemma fib_ge_three (i : ℕ) (hi : 2 ≤ i) : 3 ≤ fib i := by
  have := fib_ge_succ i (by omega); omega

/-- Elements of removeIndices fib {0,1} are all ≥ 3. -/
private lemma removeIndices_fib_ge_three {x : ℕ}
    (hx : x ∈ removeIndices fib {0, 1}) : 3 ≤ x := by
  simp only [removeIndices, Set.mem_setOf_eq] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact fib_ge_three i (by simp [Finset.mem_singleton, Finset.mem_insert] at hi; omega)

/-- fib(k+1) > fib(k) + 1 for k ≥ 2 (there's always a gap of ≥ 2). -/
private lemma fib_succ_gt_succ (k : ℕ) (hk : 2 ≤ k) : fib k + 1 < fib (k + 1) := by
  simp [fib]; show fib k + 1 < fib (k - 1) + fib k
  have : 2 ≤ fib (k - 1) := by
    have := fib_ge_succ (k - 1) (by omega); omega
  omega

/-- Partial sum identity: fib(2) + ... + fib(n) = fib(n+2) - 5 for n ≥ 2.
    Proved by induction using the Fibonacci recurrence. -/
private lemma fib_partial_sum : ∀ n, 2 ≤ n →
    (Finset.Icc 2 n).sum fib + 5 = fib (n + 2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    match n with
    | 0 => omega
    | 1 => omega
    | 2 => simp [Finset.Icc_self, fib]
    | n + 3 =>
      -- Icc 2 (n+3) = Icc 2 (n+2) ∪ {n+3}
      rw [show Finset.Icc 2 (n + 3) = Finset.Icc 2 (n + 2) ∪ {n + 3} from by
        ext x; simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega]
      rw [Finset.sum_union (by simp [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega)]
      simp only [Finset.sum_singleton]
      have ih_prev := ih (n + 2) (by omega) (by omega)
      -- Goal: (Icc 2 (n+2)).sum fib + fib (n+3) + 5 = fib (n+5)
      -- IH: (Icc 2 (n+2)).sum fib + 5 = fib (n+4)
      -- fib (n+5) = fib (n+3) + fib (n+4)
      simp [fib]; omega

/-- Core lemma: fib(k) + 1 is not a sum of distinct elements from {fib(j) | j ≥ 2}.
    Proof by strong induction on k.
    - Case A (fib(k) ∈ S): remainder 1, but all elements ≥ 3.
    - Case B1 (fib(k-1) ∈ S): remainder fib(k-2)+1, apply IH.
    - Case B2 (neither): elements ≤ fib(k-2), sum bounded by fib(k)-5 < fib(k)+1. -/
private lemma fib_plus_one_not_repr : ∀ k, 2 ≤ k →
    fib k + 1 ∉ finiteSums (removeIndices fib {0, 1}) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk ⟨S, hS_sub, hS_sum⟩
    have hge3 : ∀ x ∈ S, 3 ≤ x := fun x hx =>
      removeIndices_fib_ge_three (hS_sub (Finset.mem_coe.mpr hx))
    -- Case A: fib(k) ∈ S
    by_cases hfk : fib k ∈ S
    · -- Remainder after removing fib(k) is 1
      have hrem : (S.erase (fib k)).sum id = 1 := by
        have := Finset.sum_erase_eq_sub hfk (f := id)
        simp only [id] at this ⊢; omega
      -- But all remaining elements ≥ 3
      rcases (S.erase (fib k)).eq_empty_or_nonempty with he | ⟨x, hx⟩
      · rw [he] at hrem; simp at hrem
      · have : 3 ≤ (S.erase (fib k)).sum id :=
          le_trans (hge3 x (Finset.mem_of_mem_erase hx))
            (Finset.single_le_sum (fun a _ => Nat.zero_le _) hx)
        omega
    · -- Case B: fib(k) ∉ S
      by_cases hfk1 : fib (k - 1) ∈ S
      · -- Case B1: fib(k-1) ∈ S
        -- For k = 2: fib(1) = 2 ∈ S contradicts all elements ≥ 3
        have hk3 : 3 ≤ k := by
          by_contra h; push_neg at h
          have : k = 2 := by omega
          subst this; exact absurd (hge3 _ hfk1) (by simp [fib]; omega)
        -- Remainder = fib(k)+1-fib(k-1) = fib(k-2)+1
        have hrec : fib k = fib (k - 2) + fib (k - 1) := by
          conv_lhs => rw [show k = (k - 2) + 2 from by omega, fib]
        have hrem : (S.erase (fib (k - 1))).sum id = fib (k - 2) + 1 := by
          have := Finset.sum_erase_eq_sub hfk1 (f := id)
          simp only [id] at this ⊢; omega
        -- S.erase fib(k-1) ⊆ removeIndices fib {0,1}
        have hsub : ↑(S.erase (fib (k - 1))) ⊆ removeIndices fib {0, 1} := by
          exact Set.Subset.trans (Finset.coe_subset.mpr (Finset.erase_subset _ _)) hS_sub
        -- Apply IH: fib(k-2)+1 not representable (k-2 ≥ 2 since k ≥ 4)
        by_cases hk4 : 4 ≤ k
        · exact ih (k - 2) (by omega) (by omega) ⟨S.erase (fib (k - 1)), hsub, hrem⟩
        · -- k = 3: remainder = fib(1)+1 = 3.
          -- S.erase(fib 2) has sum 3 but excludes fib(2)=3 and fib(3)=5∉S.
          -- Remaining elements are fib(j) with j ≥ 4, each ≥ 8 > 3.
          have : k = 3 := by omega
          subst this
          rcases (S.erase (fib 2)).eq_empty_or_nonempty with he | ⟨x, hx⟩
          · rw [he] at hrem; simp at hrem
          · have hx_mem := hS_sub (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hx))
            simp only [removeIndices, Set.mem_setOf_eq] at hx_mem
            obtain ⟨j, hj, rfl⟩ := hx_mem
            have hj2 : 2 ≤ j := by
              simp [Finset.mem_singleton, Finset.mem_insert] at hj; omega
            -- fib j ≠ fib(k) = fib 3 since fib(k) ∉ S
            have hj_ne3 : j ≠ 3 := by
              intro heq; subst heq; exact hfk (Finset.mem_of_mem_erase hx)
            -- fib j ≠ fib(k-1) = fib 2 since it was erased
            have hj_ne2 : j ≠ 2 := by
              intro heq; subst heq
              exact (Finset.not_mem_erase _ _) hx
            -- So j ≥ 4, fib j ≥ fib 4 = 8
            have : 8 ≤ fib j := by
              have : 4 ≤ j := by omega
              have := fib_ge_succ j (by omega); simp [fib] at *; omega
            have : 8 ≤ (S.erase (fib 2)).sum id :=
              le_trans this (Finset.single_le_sum (fun a _ => Nat.zero_le _) hx)
            omega
      · -- Case B2: fib(k) ∉ S, fib(k-1) ∉ S
        -- All elements are fib(j) with j ≥ 2, j ≠ k, j ≠ k-1
        -- No element ≥ fib(k+1) since fib(k+1) > fib(k)+1 = S.sum
        -- So all elements are in {fib(2),...,fib(k-2)}
        -- Their sum ≤ fib(k)-5 < fib(k)+1 = S.sum, contradiction
        -- Handle small k directly
        match k with
        | 0 => omega
        | 1 => omega
        | 2 =>
          -- S ⊆ {fib j | j ≥ 2, j ≠ 2, j ≠ 1}. fib(k)=fib(2)=3, fib(k-1)=fib(1)=2.
          -- So elements are fib j with j ≥ 3, each ≥ 5. But sum = 4.
          -- Single element ≥ 5 > 4. Two elements ≥ 10 > 4.
          rcases S.eq_empty_or_nonempty with he | ⟨x, hx⟩
          · rw [he] at hS_sum; simp at hS_sum
          · have hx_ge5 : 5 ≤ x := by
              have := hS_sub (Finset.mem_coe.mpr hx)
              simp only [removeIndices, Set.mem_setOf_eq] at this
              obtain ⟨j, hj, rfl⟩ := this
              have hj2 : 2 ≤ j := by
                simp [Finset.mem_singleton, Finset.mem_insert] at hj; omega
              have hj_ne2 : j ≠ 2 := fun h => by subst h; exact hfk hx
              have : 3 ≤ j := by omega
              have := fib_ge_succ j (by omega)
              simp [fib] at *; omega
            have : 5 ≤ S.sum id :=
              le_trans hx_ge5 (Finset.single_le_sum (fun a _ => Nat.zero_le _) hx)
            omega
        | 3 =>
          -- fib(3)+1=6. fib(2)=3∉S, fib(3)=5∉S. Elements have j≥4, each≥8.
          rcases S.eq_empty_or_nonempty with he | ⟨x, hx⟩
          · rw [he] at hS_sum; simp at hS_sum
          · have hx_ge8 : 8 ≤ x := by
              have := hS_sub (Finset.mem_coe.mpr hx)
              simp only [removeIndices, Set.mem_setOf_eq] at this
              obtain ⟨j, hj, rfl⟩ := this
              have hj2 : 2 ≤ j := by
                simp [Finset.mem_singleton, Finset.mem_insert] at hj; omega
              have hj_ne3 : j ≠ 3 := fun h => by subst h; exact hfk hx
              have hj_ne2 : j ≠ 2 := fun h => by subst h; exact hfk1 hx
              have : 4 ≤ j := by omega
              have := fib_ge_succ j (by omega); simp [fib] at *; omega
            have : 8 ≤ S.sum id :=
              le_trans hx_ge8 (Finset.single_le_sum (fun a _ => Nat.zero_le _) hx)
            omega
        | k + 4 =>
          -- General case: k+4 ≥ 4.
          -- All elements of S are fib(j) for 2 ≤ j ≤ k+2 (j ≠ k+3,k+4, j≥k+5 too big).
          -- S ⊆ image fib (Icc 2 (k+2)), so S.sum ≤ (Icc 2 (k+2)).sum fib = fib(k+4)-5.
          -- But S.sum = fib(k+4)+1, contradiction.
          have hS_sub_img : S ⊆ (Finset.Icc 2 (k + 2)).image fib := by
            intro x hx
            have hx_ri := hS_sub (Finset.mem_coe.mpr hx)
            simp only [removeIndices, Set.mem_setOf_eq] at hx_ri
            obtain ⟨j, hj, rfl⟩ := hx_ri
            have hj2 : 2 ≤ j := by
              simp [Finset.mem_singleton, Finset.mem_insert] at hj; omega
            refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj2, ?_⟩, rfl⟩
            -- Show j ≤ k + 2: j ≠ k+3 (from hfk1), j ≠ k+4 (from hfk), j < k+5 (too big)
            by_contra hjg; push_neg at hjg
            rcases show j = k + 3 ∨ j = k + 4 ∨ k + 5 ≤ j from by omega with rfl | rfl | hjg5
            · exact hfk1 hx
            · exact hfk hx
            · have : fib (k + 4) + 1 < fib j :=
                lt_of_lt_of_le (fib_succ_gt_succ (k + 4) (by omega))
                  (fib_strictMono.monotone (by omega : k + 5 ≤ j))
              have : fib j ≤ S.sum id :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
              omega
          have hS_bound : S.sum id ≤ (Finset.Icc 2 (k + 2)).sum fib := by
            calc S.sum id
                ≤ ((Finset.Icc 2 (k + 2)).image fib).sum id :=
                  Finset.sum_le_sum_of_subset_of_nonneg hS_sub_img (fun _ _ _ => Nat.zero_le _)
              _ = (Finset.Icc 2 (k + 2)).sum (id ∘ fib) :=
                  Finset.sum_image (fun i _ j _ h => fib_strictMono.injective h)
              _ = (Finset.Icc 2 (k + 2)).sum fib := by congr
          have := fib_partial_sum (k + 2) (by omega)
          omega

/-- Fibonacci sequence is not 2-robust: removing indices {0, 1} breaks completeness.
    Proof: for any N, the number fib(max N 2) + 1 ≥ N is not representable
    by {fib(j) | j ≥ 2}, giving infinitely many non-representable numbers.
    Previously axiomatized; now proved via fib_plus_one_not_repr. -/
theorem fib_not_2_robust : NotRobust fib 2 := by
  refine ⟨{0, 1}, by simp, ?_⟩
  intro ⟨N, hN⟩
  have hk : 2 ≤ max N 2 := le_max_right _ _
  have hN_le : N ≤ fib (max N 2) + 1 := by
    calc N ≤ max N 2 := le_max_left _ _
      _ ≤ max N 2 + 1 := Nat.le_succ _
      _ ≤ fib (max N 2) + 1 := by
        have := fib_ge_succ (max N 2) (by omega); omega
  exact fib_plus_one_not_repr (max N 2) hk (hN (fib (max N 2) + 1) hN_le)

/-- (1, 2) is a valid pair -/
theorem pair_1_2_valid : (1, 2) ∈ validPairs := by
  constructor
  · norm_num
  · use fib
    constructor
    · -- Fibonacci is monotone: fib n ≤ fib (n+1) for all n
      exact monotone_nat_of_le_succ (fun n => by
        cases n with
        | zero => show (1 : ℕ) ≤ 2; norm_num
        | succ k => show fib (k + 1) ≤ fib k + fib (k + 1); omega)
    constructor
    · exact fib_complete
    constructor
    · exact fib_1_robust
    · exact fib_not_2_robust

/-
## The Main Conjecture

The question asks to characterize all valid pairs (m, n) with m < n.
-/

/-- Erdős Problem #348 (Open): Characterize the valid pairs.
    One conjecture: valid pairs are exactly {(m, m+1) : m ∈ ℕ}.
    Alternatively, there may be a cutoff after which no more valid pairs exist. -/
def erdos_348_characterization : Prop :=
  validPairs = {p : ℕ × ℕ | p.1 < p.2 ∧ p.2 = p.1 + 1} ∨
  (∃ k : ℕ, validPairs = {p : ℕ × ℕ | p.1 < p.2 ∧ p.1 < k})

/-- The case (2, 3) is unknown — but the disjunction is trivially decidable. -/
theorem erdos_348_case_2_3 :
    (2, 3) ∈ validPairs ∨ (2, 3) ∉ validPairs :=
  em _

/-- Strong robustness version -/
def IsStronglyRobust (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → IsStronglyComplete (removeIndices a S)

/-- **Known results (not formalized, for reference):**
- Van Doorn's theorem: no strongly complete sequence is 2-robust
  (∀ a, Monotone a → IsStronglyComplete (sequenceToSet a) → ¬IsStronglyRobust a 2)
- Complete sequences have bounded gaps eventually
- IsComplete A ↔ ∃ N, ∀ n ≥ N, representationCount > 0
  (requires finiteness: any S with S.sum = n satisfies S ⊆ Finset.range(n+1)) -/

/-
## The Main Open Question

The precise characterization of valid pairs remains unknown.
-/

/--
Erdős Problem #348 (Open):

Characterize all pairs (m, n) with 0 ≤ m < n such that there exists a
complete sequence remaining complete after removing any m elements but
becoming incomplete after removing some n elements.

Known:
- (0, 1) is valid (powers of 2)
- (1, 2) is valid (Fibonacci)
- For strongly complete sequences, nothing with m ≥ 2 works (van Doorn)

Unknown:
- Is (2, 3) valid for the weaker completeness notion?
- What is the full characterization?
-/
def erdos_348_main_problem : Prop :=
  (∀ m : ℕ, (m, m + 1) ∈ validPairs) ∨
  (∃ k : ℕ, ∀ m ≥ k, (m, m + 1) ∉ validPairs)

end Erdos348
