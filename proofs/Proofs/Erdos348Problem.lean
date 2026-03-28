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

/-- Fibonacci sequence is complete (Zeckendorf's theorem).
    Deep result: every positive integer is a sum of non-consecutive Fibonacci numbers. -/
axiom fib_complete : IsComplete (sequenceToSet fib)

/-- Fibonacci sequence is 1-robust: removing one element doesn't break completeness.
    Deep result about the redundancy structure of Fibonacci representations. -/
axiom fib_1_robust : IsRobust fib 1

/-- Fibonacci sequence is not 2-robust: removing indices {0, 1} breaks completeness.
    After removal, the sequence {3, 5, 8, 13, ...} has infinitely many gaps:
    numbers of the form fib(k)-1 (for k ≥ 3) are never subset sums of
    smaller Fibonacci numbers, by a recursive complement argument. -/
axiom fib_not_2_robust : NotRobust fib 2

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
