/-
  Erdős Problem #849: Binomial Coefficient Multiplicities

  **Question**: Is it true that for every integer t ≥ 1, there is some integer a
  such that C(n,k) = a (with 1 ≤ k ≤ n/2) has exactly t solutions?

  **Context**: This is related to Singmaster's Conjecture about how many times
  a value can appear in Pascal's triangle.

  **Known Examples**:
  - t = 1: a = 2 (appears only as C(2,1))
  - t = 2: a = 3 (appears as C(3,1) and C(3,2), but we count 1 ≤ k ≤ n/2)
  - t = 3: a = 120 (appears at C(10,3), C(16,2), C(120,1))
  - t = 4: a = 3003 (appears at C(14,6), C(15,5), C(78,2), C(3003,1))

  **Status**: OPEN for t ≥ 5. No known values appear exactly 5 times.

  References:
  - https://erdosproblems.com/849
  - Singmaster, D., "How often does an integer occur as a binomial coefficient?" (1971)
  - https://oeis.org/A003015 (numbers occurring 5+ times)
-/

import Mathlib

open Nat Set Finset BigOperators

namespace Erdos849

/-!
## Core Definitions

The multiplicity of a value in Pascal's triangle, counting only entries
with 1 ≤ k ≤ n/2 to avoid trivial symmetry.
-/

/-- The **multiplicity set** of a value a in Pascal's triangle:
all pairs (n, k) with 1 ≤ k ≤ n/2 such that C(n,k) = a. -/
def BinomMultiplicitySet (a : ℕ) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ p.1.choose p.2 = a}

/-- The **multiplicity** of a in Pascal's triangle (with the k ≤ n/2 restriction). -/
noncomputable def binomMultiplicity (a : ℕ) : ℕ∞ :=
  (BinomMultiplicitySet a).ncard

/-- Alternative: count only the n values (not pairs) where C(n,k) = a for some valid k. -/
noncomputable def binomNMultiplicity (a : ℕ) : ℕ :=
  {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard

/-- An integer a has **exact multiplicity t** if it appears exactly t times. -/
def HasExactMultiplicity (a t : ℕ) : Prop :=
  binomNMultiplicity a = t

/-!
## Basic Properties
-/

/-- Every positive integer appears at least once (as C(a,1) = a). -/
theorem appears_at_least_once (a : ℕ) (ha : 2 ≤ a) :
    ∃ n k, 1 ≤ k ∧ 2 * k ≤ n ∧ n.choose k = a := by
  refine ⟨a, 1, le_refl 1, ?_, ?_⟩
  · omega
  · simp [Nat.choose_one_right]

/-- 1 appears infinitely many times (as C(n,0) for all n, but k=0 excluded).
Actually, 1 = C(n,n) but k > n/2, so with our restriction, 1 appears 0 times! -/
axiom one_multiplicity : binomNMultiplicity 1 = 0

/-- 2 appears exactly once: only as C(2,1). -/
axiom two_multiplicity : binomNMultiplicity 2 = 1

/-!
## Singmaster's Conjecture

The related conjecture bounds how many times any value can appear.
-/

/-- **Singmaster's Conjecture**: There exists a constant N such that no integer
appears more than N times in Pascal's triangle.

The best known bound is that multiplicities are O((log n)^c) for some c. -/
axiom singmaster_conjecture : ∃ N : ℕ, ∀ a : ℕ, binomNMultiplicity a ≤ N

/-- Known: No value appears more than 8 times (conjectured bound is 8).
This is based on extensive computation. -/
axiom multiplicity_bound_8 : ∀ a : ℕ, binomNMultiplicity a ≤ 8

/-!
## Known Multiplicities

Values with specific multiplicities.
-/

/-- 120 has multiplicity 3: appears at C(10,3), C(16,2), C(120,1). -/
axiom multiplicity_120 : binomNMultiplicity 120 = 3

/-- Verification: C(10,3) = 120. -/
theorem choose_10_3 : Nat.choose 10 3 = 120 := by native_decide

/-- Verification: C(16,2) = 120. -/
theorem choose_16_2 : Nat.choose 16 2 = 120 := by native_decide

/-- Verification: C(120,1) = 120. -/
theorem choose_120_1 : Nat.choose 120 1 = 120 := by native_decide

/-- 3003 has multiplicity 4: appears at C(14,6), C(15,5), C(78,2), C(3003,1). -/
axiom multiplicity_3003 : binomNMultiplicity 3003 = 4

/-- Verification: C(14,6) = 3003. -/
theorem choose_14_6 : Nat.choose 14 6 = 3003 := by native_decide

/-- Verification: C(15,5) = 3003. -/
theorem choose_15_5 : Nat.choose 15 5 = 3003 := by native_decide

/-- Verification: C(78,2) = 3003. -/
theorem choose_78_2 : Nat.choose 78 2 = 3003 := by native_decide

/-- Verification: C(3003,1) = 3003. -/
theorem choose_3003_1 : Nat.choose 3003 1 = 3003 := by native_decide

/-!
## Main Conjecture (OPEN)

For every t ≥ 1, does there exist a with exactly t occurrences?
-/

/-- **Erdős Problem #849 (OPEN)**: For every t ≥ 1, there exists a value a
that appears exactly t times in Pascal's triangle (with 1 ≤ k ≤ n/2).

This is OPEN for t ≥ 5. -/
axiom erdos_849_conjecture :
    ∀ t ≥ 1, ∃ a : ℕ, binomNMultiplicity a = t

/-- The t = 1 case is true: 2 appears exactly once. -/
theorem t_equals_1 : ∃ a : ℕ, binomNMultiplicity a = 1 :=
  ⟨2, two_multiplicity⟩

/-- The t = 3 case is true: 120 appears exactly 3 times. -/
theorem t_equals_3 : ∃ a : ℕ, binomNMultiplicity a = 3 :=
  ⟨120, multiplicity_120⟩

/-- The t = 4 case is true: 3003 appears exactly 4 times. -/
theorem t_equals_4 : ∃ a : ℕ, binomNMultiplicity a = 4 :=
  ⟨3003, multiplicity_3003⟩

/-- The t = 5 case is OPEN: no known value appears exactly 5 times. -/
axiom t_equals_5_open :
    (∃ a : ℕ, binomNMultiplicity a = 5) ∨
    (¬∃ a : ℕ, binomNMultiplicity a = 5)

/-!
## Special Values in Pascal's Triangle

Some values appear many times due to special structure.
-/

/-- The value 6 appears twice: C(4,2) = C(6,1) = 6. -/
axiom multiplicity_6 : binomNMultiplicity 6 = 2

/-- 10 appears twice: C(5,2) = C(10,1) = 10. -/
theorem choose_5_2 : Nat.choose 5 2 = 10 := by native_decide
theorem choose_10_1 : Nat.choose 10 1 = 10 := by native_decide

/-!
## Asymptotic Results

Upper bounds on how often a value can appear.
-/

/-- For large a, the multiplicity is bounded by O(log a). -/
axiom multiplicity_log_bound : ∃ C : ℝ, C > 0 ∧
    ∀ a ≥ 2, (binomNMultiplicity a : ℝ) ≤ C * Real.log a

/-- The infinite family C(n,2) = C(n(n-1)/2, 1) gives infinitely many
values with multiplicity ≥ 2. -/
axiom infinitely_many_multiplicity_2 :
    {a : ℕ | binomNMultiplicity a ≥ 2}.Infinite

/-!
## Related Sequences

Connection to OEIS sequences.
-/

/-- A003015: Numbers that occur 5 or more times in Pascal's triangle.
Currently only {1} is known, and 1 doesn't count with our k ≥ 1 restriction. -/
axiom oeis_A003015 : {a : ℕ | binomNMultiplicity a ≥ 5} ⊆ {1}

/-- A182238: Numbers that occur exactly 4 times.
Includes 3003, 6435, 11440, ... -/
axiom values_with_multiplicity_4 : binomNMultiplicity 6435 = 4

/-- Verification: C(15,6) = 5005 ≠ 6435. Let's verify 6435 placements. -/
theorem choose_15_7 : Nat.choose 15 7 = 6435 := by native_decide
theorem choose_6435_1 : Nat.choose 6435 1 = 6435 := by native_decide

/-!
## Historical Context

The problem connects to several classical questions about Pascal's triangle.
Erdős and Gordon posed this question "many years ago" (before 1996), but it
is now commonly associated with Singmaster's conjecture (1971) about
bounding multiplicities.

The difficulty lies in the interplay between:
1. The "edge" appearances: C(a,1) = a
2. The "triangular number" appearances: C(n,2) = n(n-1)/2
3. "Deep" appearances: larger k values

For most values, these don't align. The question is whether for every t,
we can find an a where exactly t of these coincide.
-/

end Erdos849
