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

/-!
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

/-!
## Basic Properties
-/

/-- 0 is always in D(n) when n is a perfect square. -/
axiom zero_mem_factorDifferenceSet_of_sq (n : ℕ) (hn : IsSquare n) :
    0 ∈ factorDifferenceSet n

/-- For n > 0, D(n) always contains n - 1 (from factorization n = 1 · n). -/
axiom pred_mem_factorDifferenceSet (n : ℕ) (hn : 0 < n) :
    n - 1 ∈ factorDifferenceSet n

/-- D(1) = {0} since 1 = 1 · 1 is the only factorization. -/
axiom factorDifferenceSet_one : factorDifferenceSet 1 = {0}

/-- D(p) = {p - 1} for prime p (only factorization is 1 · p). -/
axiom factorDifferenceSet_prime (p : ℕ) (hp : p.Prime) :
    factorDifferenceSet p = {p - 1}

/-!
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
axiom erdos_885_conjecture : ∀ k ≥ 1, ∃ Ns : Finset ℕ, IsKCommonSet k Ns

/-!
## Solved Cases
-/

/-- **Erdős-Rosenfeld (1997)**: The case k = 2 is true.

Example: N₁ = 6, N₂ = 12
- D(6) = {5, 1} (from 1·6, 2·3)
- D(12) = {11, 4, 1} (from 1·12, 2·6, 3·4)
- D(6) ∩ D(12) ⊇ {1} with |intersection| ≥ 2 achieved elsewhere. -/
axiom erdos_rosenfeld_k2 : ∃ Ns : Finset ℕ, IsKCommonSet 2 Ns

/-- **Jiménez-Urroz (1999)**: The case k = 3 is true.

The construction requires finding three highly composite numbers with
many common factor differences. -/
axiom jimenez_urroz_k3 : ∃ Ns : Finset ℕ, IsKCommonSet 3 Ns

/-- **Bremner (2019)**: The case k = 4 is true.

Bremner used computational search combined with number-theoretic
techniques to find four integers with ≥ 4 common factor differences. -/
axiom bremner_k4 : ∃ Ns : Finset ℕ, IsKCommonSet 4 Ns

/-!
## The Open Case: k ≥ 5

The conjecture remains open for all k ≥ 5. The difficulty increases
rapidly because:
1. More integers are needed
2. Each must have many factors
3. Their D(N) sets must align on ≥ k common values
-/

/-- **OPEN**: Does there exist a 5-common set? -/
axiom open_k5 :
    (∃ Ns : Finset ℕ, IsKCommonSet 5 Ns) ∨
    (¬∃ Ns : Finset ℕ, IsKCommonSet 5 Ns)

/-!
## Computational Observations
-/

/-- The number of elements in D(n) equals the number of divisor pairs.
For n with d(n) divisors, |D(n)| = ⌈d(n)/2⌉. -/
axiom card_factorDifferenceSet (n : ℕ) (hn : 0 < n) :
    (factorDifferenceSet n).ncard = (n.divisors.card + 1) / 2

/-- Highly composite numbers have larger factor difference sets,
making them good candidates for finding common elements. -/
axiom highly_composite_larger_D :
    ∀ n m : ℕ, 0 < n → 0 < m →
      n.divisors.card < m.divisors.card →
      (factorDifferenceSet n).ncard ≤ (factorDifferenceSet m).ncard

/-!
## Connection to Divisor Structure
-/

/-- D(n) can be characterized in terms of divisors:
d ∈ D(n) iff there exists a divisor a of n with |a - n/a| = d. -/
axiom mem_factorDifferenceSet_iff_divisor (n : ℕ) (hn : 0 < n) (d : ℕ) :
    d ∈ factorDifferenceSet n ↔
    ∃ a ∈ n.divisors, d = Int.natAbs ((a : ℤ) - (n / a : ℤ))

/-!
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

/-!
## Intersection Properties
-/

/-- 1 is in the intersection D(6) ∩ D(12). -/
theorem one_mem_intersection_D6_D12 :
    1 ∈ factorDifferenceSet 6 ∩ factorDifferenceSet 12 :=
  ⟨one_mem_D_6, one_mem_D_12⟩

/-!
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
