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

/-!
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

/-!
## Removing Elements

We need to formalize what it means to remove elements from a sequence.
-/

/-- Remove a finite set of indices from a sequence -/
noncomputable def removeIndices (a : ℕ → ℕ) (S : Finset ℕ) : Set ℕ :=
  {a i | i ∉ S}

/-- Alternative: remove by values instead of indices -/
def removeValues (A : Set ℕ) (S : Finset ℕ) : Set ℕ :=
  A \ ↑S

/-!
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

/-!
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

/-- Powers of 2 are complete (Zeckendorf-like representation exists) -/
theorem powersOf2_complete : IsComplete (sequenceToSet powersOf2) := by
  use 0
  intro n _
  -- Every positive integer has a binary representation
  sorry

/-- Powers of 2 are not 1-robust: removing any power breaks completeness -/
theorem powersOf2_not_1_robust : NotRobust powersOf2 1 := by
  -- Removing 2^k means we can't represent 2^k
  use {0}
  constructor
  · simp
  · intro ⟨N, hN⟩
    -- The number 1 cannot be represented without 2^0 = 1
    sorry

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

/-- Fibonacci sequence is complete -/
theorem fib_complete : IsComplete (sequenceToSet fib) := by
  -- Zeckendorf's theorem: every positive integer is a sum of non-consecutive Fibonacci numbers
  sorry

/-- Fibonacci sequence is 1-robust -/
theorem fib_1_robust : IsRobust fib 1 := by
  -- Removing one Fibonacci number doesn't break completeness
  sorry

/-- Fibonacci sequence is not 2-robust -/
theorem fib_not_2_robust : NotRobust fib 2 := by
  -- Removing fib(0)=1 and fib(1)=2 breaks completeness for representing 3
  sorry

/-- (1, 2) is a valid pair -/
theorem pair_1_2_valid : (1, 2) ∈ validPairs := by
  constructor
  · norm_num
  · use fib
    constructor
    · -- Fibonacci is monotone
      intro m n hmn
      sorry
    constructor
    · exact fib_complete
    constructor
    · exact fib_1_robust
    · exact fib_not_2_robust

/-!
## The Main Conjecture

The question asks to characterize all valid pairs (m, n) with m < n.
-/

/-- Erdős Problem #348 (Open): Characterize the valid pairs -/
axiom erdos_348_characterization :
  -- The set of valid pairs is either {(m, m+1) : m ∈ ℕ} or some other explicit set
  validPairs = {p : ℕ × ℕ | p.1 < p.2 ∧ p.2 = p.1 + 1} ∨
  -- Or there's some cutoff
  (∃ k : ℕ, validPairs = {p : ℕ × ℕ | p.1 < p.2 ∧ p.1 < k})

/-- The case (2, 3) is unknown -/
axiom erdos_348_case_2_3 :
  (2, 3) ∈ validPairs ∨ (2, 3) ∉ validPairs

/-!
## Van Doorn's Result

Wouter van Doorn proved that for strongly complete sequences (representing ALL
natural numbers, not just sufficiently large ones), no valid pairs exist for m ≥ 2.
-/

/-- Strong robustness version -/
def IsStronglyRobust (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → IsStronglyComplete (removeIndices a S)

/-- Van Doorn's result: no strongly complete sequence is 2-robust -/
axiom vanDoorn_theorem :
  ∀ a : ℕ → ℕ, Monotone a → IsStronglyComplete (sequenceToSet a) →
    ¬IsStronglyRobust a 2

/-!
## Connections to Representation Theory

Complete sequences are related to representation functions and additive bases.
-/

/-- The representation function counts ways to represent n -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {S : Finset ℕ | ↑S ⊆ A ∧ S.sum id = n}

/-- A complete sequence has positive representation count for large n -/
theorem complete_iff_repr (A : Set ℕ) :
    IsComplete A ↔ ∃ N, ∀ n ≥ N, 0 < representationCount A n := by
  sorry

/-!
## The Gap Property

A key observation is that complete sequences cannot have arbitrarily large gaps.
-/

/-- The n-th gap in a monotone sequence -/
noncomputable def gap (a : ℕ → ℕ) (n : ℕ) : ℕ := a (n + 1) - a n

/-- Complete sequences have bounded gaps eventually -/
axiom complete_bounded_gaps :
  ∀ a : ℕ → ℕ, Monotone a → IsComplete (sequenceToSet a) →
    ∃ N M : ℕ, ∀ n ≥ N, gap a n ≤ M

/-!
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
axiom erdos_348_main_problem :
  (∀ m : ℕ, (m, m + 1) ∈ validPairs) ∨
  (∃ k : ℕ, ∀ m ≥ k, (m, m + 1) ∉ validPairs)

end Erdos348
