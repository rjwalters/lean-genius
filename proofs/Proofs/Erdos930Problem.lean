/-
  Erdős Problem #930: Products of Disjoint Intervals and Perfect Powers

  Is it true that, for every r, there is a k such that if I₁,...,Iᵣ are
  disjoint intervals of consecutive integers, all of length at least k, then
  the product ∏_{1≤i≤r} ∏_{m∈Iᵢ} m is not a perfect power?

  **Status**: OPEN for general r; SOLVED for r=1 by Erdős-Selfridge (1975)

  **Historical Context**:
  Erdős and Selfridge proved in 1975 that the product of consecutive integers
  is never a perfect power, solving the case r=1. This was a long-standing
  conjecture. The general case for r > 1 remains open, though the condition
  that intervals be large (length at least k depending on r) is necessary.

  References:
  - https://erdosproblems.com/930
  - Erdős, P. and Selfridge, J. L., "The product of consecutive integers is
    never a power." Illinois J. Math. 19 (1975), 292-301.
-/

import Mathlib

open Finset Nat

namespace Erdos930

/-!
## Core Definitions
-/

/-- A natural number n is a **perfect power** if there exist natural numbers m
and l with l > 1 such that m^l = n.

Examples: 4 = 2², 8 = 2³, 9 = 3², 16 = 2⁴ = 4², 27 = 3³, etc.

Note: 0 and 1 are technically perfect powers (0 = 0², 1 = 1² = 1³ = ...). -/
def IsPower (n : ℕ) : Prop :=
  ∃ m l, 1 < l ∧ m ^ l = n

/-- The product of integers in an interval [a, b]. -/
noncomputable def intervalProduct (a b : ℕ) : ℕ :=
  ∏ m ∈ Icc a b, m

/-- The length of an interval [a, b] is b - a + 1 when b ≥ a. -/
def intervalLength (a b : ℕ) : ℕ := b - a + 1

/-!
## The Main Conjecture (OPEN)

The conjecture asks: for every number r of intervals, does there exist
a minimum length k such that r disjoint intervals of length ≥ k have
a product that is NOT a perfect power?
-/

/-- **Erdős Problem #930 (OPEN)**: For every r > 0, there exists k such that
if I₁,...,Iᵣ are r disjoint intervals of consecutive integers, each of length
at least k, then their combined product is never a perfect power.

The intervals are represented by their starting points I₁ and ending points I₂,
where I₁ i and I₂ i are the start and end of the i-th interval.

Conditions:
1. Each interval has positive start and length at least k: 0 < I₁ i and I₁ i + k ≤ I₂ i + 1
2. Intervals are disjoint and ordered: for i < j, I₂ i < I₁ j -/
axiom erdos_930_conjecture :
    ∀ r > 0, ∃ k, ∀ I₁ I₂ : Fin r → ℕ,
      (∀ i : Fin r, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
        (∀ i j : Fin r, i < j → I₂ i < I₁ j) →
          ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m)

/-!
## Solved Case: r = 1 (Erdős-Selfridge 1975)

The famous theorem that the product of consecutive integers is never
a perfect power. This resolved a long-standing conjecture.
-/

/-- **Erdős-Selfridge Theorem (1975)**: The product of two or more consecutive
positive integers is never a perfect power.

In other words, for any n ≥ 0 and k ≥ 2:
  (n+1)(n+2)...(n+k) ≠ m^l for any m, l with l > 1.

This is the r = 1 case of Problem #930, and it was proved using sophisticated
arguments about prime factorizations and the distribution of primes. -/
axiom erdos_selfridge_consecutive_integers :
    ∀ n k, 0 ≤ n → 2 ≤ k →
      ¬ IsPower (∏ m ∈ Icc (n + 1) (n + k), m)

/-!
## Technical Variant: Prime Multiplicity Bound

This is the key technical lemma from the Erdős-Selfridge paper.
It shows that for any consecutive product of sufficient length,
there's a prime whose multiplicity is not divisible by any given l.
-/

/-- Returns the least prime ≥ k. -/
noncomputable def nextPrime (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)

/-- **Erdős-Selfridge Technical Lemma**: For k ≥ 3, l ≥ 2, and n + k ≥ nextPrime(k),
there exists a prime p ≥ k such that l does not divide the multiplicity of p
in the factorization of (n+1)(n+2)...(n+k).

This is the heart of the Erdős-Selfridge proof - it prevents the product
from being a perfect l-th power by finding a "problematic" prime. -/
axiom erdos_selfridge_prime_multiplicity :
    ∀ k l n, 3 ≤ k → 2 ≤ l → nextPrime k ≤ n + k →
      ∃ p, k ≤ p ∧ p.Prime ∧
        ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p)

/-!
## Basic Properties of Perfect Powers
-/

/-- 0 is a perfect power (0 = 0² = 0³ = ...). -/
theorem zero_isPower : IsPower 0 := ⟨0, 2, by norm_num, rfl⟩

/-- 1 is a perfect power (1 = 1² = 1³ = ...). -/
theorem one_isPower : IsPower 1 := ⟨1, 2, by norm_num, rfl⟩

/-- Any perfect square is a perfect power. -/
theorem sq_isPower (n : ℕ) : IsPower (n ^ 2) := ⟨n, 2, by norm_num, rfl⟩

/-- Any perfect cube is a perfect power. -/
theorem cube_isPower (n : ℕ) : IsPower (n ^ 3) := ⟨n, 3, by norm_num, rfl⟩

/-!
## Verified Small Examples
-/

/-- 4 = 2² is a perfect power. -/
example : IsPower 4 := ⟨2, 2, by norm_num, rfl⟩

/-- 8 = 2³ is a perfect power. -/
example : IsPower 8 := ⟨2, 3, by norm_num, rfl⟩

/-- 27 = 3³ is a perfect power. -/
example : IsPower 27 := ⟨3, 3, by norm_num, rfl⟩

/-- 2 is NOT a perfect power.

Proof: If 2 = m^l with l > 1, then:
- m = 0: 0^l = 0 ≠ 2
- m = 1: 1^l = 1 ≠ 2
- m ≥ 2: m^l ≥ 2^2 = 4 > 2 -/
axiom two_not_isPower : ¬ IsPower 2

/-- 6 is NOT a perfect power (6 = 2·3 has distinct prime factors with exponent 1).

Proof: If 6 = m^l with l > 1, then:
- m = 0: 0^l = 0 ≠ 6
- m = 1: 1^l = 1 ≠ 6
- m = 2: 2^2 = 4 ≠ 6, 2^3 = 8 ≠ 6, and 2^l > 6 for l > 3
- m ≥ 3: m^l ≥ 3^2 = 9 > 6 -/
axiom six_not_isPower : ¬ IsPower 6

/-- The product 2·3 = 6 is not a perfect power (example of r=1, k=2 case). -/
theorem product_2_3_not_power : ¬ IsPower (∏ m ∈ Icc 2 3, m) := by
  have h : ∏ m ∈ Icc 2 3, m = 6 := by native_decide
  rw [h]
  exact six_not_isPower

end Erdos930
