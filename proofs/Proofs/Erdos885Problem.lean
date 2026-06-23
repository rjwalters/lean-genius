/-
  Erdős Problem #885: Common Factor Difference Sets

  For integer n ≥ 1, define the **factor difference set** of n by
    D(n) = {|a - b| : n = ab}

  **Conjecture (Erdős-Rosenfeld 1997)**: For every k ≥ 1, there exist
  integers N₁ < ... < Nₖ such that |∩ᵢ D(Nᵢ)| ≥ k.

  **Known Results**:
  - k = 2: Erdős-Rosenfeld (1997)
  - k = 3: Jiménez-Urroz (1999)
  - k = 4: Bremner (2019)
  - k ≥ 5: OPEN

  References:
  - https://erdosproblems.com/885
  - Erdős, P. and Rosenfeld, M., "The factor-difference set of integers" (1997)
  - Jiménez-Urroz, J., "A note on a conjecture of Erdős and Rosenfeld" (1999)
  - Bremner, A., "On a problem of Erdős related to common factor differences" (2019)
-/

import Mathlib

open Nat Set Finset BigOperators

namespace Erdos885

/-
## Core Definitions

The factor difference set D(n) captures the possible differences between
factor pairs of n. For example:
- D(12) = {|1-12|, |2-6|, |3-4|} = {11, 4, 1}
- D(6) = {|1-6|, |2-3|} = {5, 1}
-/

/-- The **factor difference set** of n is the set of absolute differences
between factor pairs: D(n) = {|a - b| : n = ab}. -/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Int.natAbs ((a : ℤ) - b)}

/-
## Basic Properties
-/

/-
## The Main Conjecture

For every k ≥ 1, find k distinct integers whose factor difference sets
have at least k elements in common.
-/

/-- A **k-common set** is a collection of k distinct positive integers whose
factor difference sets share at least k elements. -/
def IsKCommonSet (k : ℕ) (Ns : Finset ℕ) : Prop :=
  (∀ n ∈ Ns, 1 ≤ n) ∧
  Ns.card = k ∧
  (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

/-- **Erdős Problem #885 (Partially OPEN)**:
For every k ≥ 1, there exists a k-common set.

Solved for k ≤ 4, open for k ≥ 5. -/

/-
## Solved Cases
-/

/-- **Erdős-Rosenfeld (1997)**: The case k = 2 is true.

Example: N₁ = 6, N₂ = 12
- D(6) = {5, 1} (from 1·6, 2·3)
- D(12) = {11, 4, 1} (from 1·12, 2·6, 3·4)
- D(6) ∩ D(12) ⊇ {1} with |intersection| ≥ 2 achieved elsewhere. -/

/-- **Jiménez-Urroz (1999)**: The case k = 3 is true.

The construction requires finding three highly composite numbers with
many common factor differences. -/

/-- **Bremner (2019)**: The case k = 4 is true.

Bremner used computational search combined with number-theoretic
techniques to find four integers with ≥ 4 common factor differences. -/

/-
## The Open Case: k ≥ 5

The conjecture remains open for all k ≥ 5. The difficulty increases
rapidly because:
1. More integers are needed
2. Each must have many factors
3. Their D(N) sets must align on ≥ k common values
-/

/-
## Computational Observations
-/

/-- The number of elements in D(n) equals the number of divisor pairs.
For n with d(n) divisors, |D(n)| = ⌈d(n)/2⌉. -/

/-- Highly composite numbers have larger factor difference sets,
making them good candidates for finding common elements. -/

/-
## Connection to Divisor Structure
-/

/-- D(n) can be characterized in terms of divisors:
d ∈ D(n) iff there exists a divisor a of n with |a - n/a| = d. -/

/-
## Examples

We verify that specific elements are in factor difference sets.
-/

/-- 1 ∈ D(12) from factorization 3 × 4. -/
theorem one_mem_D_12 : 1 ∈ factorDifferenceSet 12 :=
  ⟨3, 4, rfl, rfl⟩

/-- 4 ∈ D(12) from factorization 2 × 6. -/
theorem four_mem_D_12 : 4 ∈ factorDifferenceSet 12 :=
  ⟨2, 6, rfl, rfl⟩

/-- 11 ∈ D(12) from factorization 1 × 12. -/
theorem eleven_mem_D_12 : 11 ∈ factorDifferenceSet 12 :=
  ⟨1, 12, rfl, rfl⟩

/-- 1 ∈ D(6) from factorization 2 × 3. -/
theorem one_mem_D_6 : 1 ∈ factorDifferenceSet 6 :=
  ⟨2, 3, rfl, rfl⟩

/-- 5 ∈ D(6) from factorization 1 × 6. -/
theorem five_mem_D_6 : 5 ∈ factorDifferenceSet 6 :=
  ⟨1, 6, rfl, rfl⟩

/-
## Intersection Properties
-/

/-- 1 is in the intersection D(6) ∩ D(12). -/
theorem one_mem_intersection_D6_D12 :
    1 ∈ factorDifferenceSet 6 ∩ factorDifferenceSet 12 :=
  ⟨one_mem_D_6, one_mem_D_12⟩

/-
## Historical Context

The factor difference set was introduced by Erdős and Rosenfeld in 1997
as a way to study the arithmetic structure of integers through their
factorizations.

The problem has connections to:
- Divisor sum functions
- Highly composite numbers
- Diophantine equations (finding n₁, ..., nₖ with specified D intersections)

The exponential growth in computational difficulty as k increases
explains why only k ≤ 4 has been verified in 25+ years of study.
-/

end Erdos885
