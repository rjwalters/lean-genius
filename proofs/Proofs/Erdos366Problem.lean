/-
  Erdős Problem #366: Consecutive k-Full Numbers

  Are there any 2-full n such that n+1 is 3-full?

  **Definitions**:
  - n is k-full if for every prime p dividing n, we have p^k | n
  - 2-full = powerful = squareful (every prime factor appears at least squared)
  - 3-full = cubeful (every prime factor appears at least cubed)

  **Known Results**:
  - (8, 9): 8 = 2³ is 3-full, 9 = 3² is 2-full (reverse direction)
  - (12167, 12168): 12167 = 23³ is 3-full, 12168 = 2³ × 3² × 13² is 2-full
  - No 2-full n with 3-full n+1 known (OPEN as of 2024)
  - No other 3-full/2-full pairs below 10^22

  References:
  - https://erdosproblems.com/366
  - Golomb, S.W., "Powerful numbers" (1970)
  - Guy, R.K., "Unsolved Problems in Number Theory" (2004), Problem B16
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

open Nat Finset

namespace Erdos366

/-
## Background: k-Full Numbers

A natural number n is **k-full** if every prime factor p of n appears
with multiplicity at least k. Equivalently, p | n implies p^k | n.

Special cases:
- 1-full: all positive integers
- 2-full: powerful numbers (also called squareful)
- 3-full: cubeful numbers
-/

/-- n is k-full if every prime factor of n appears with multiplicity ≥ k.
That is, if p | n then p^k | n. Equivalently, n.factorization p ≥ k for all p | n. -/
def IsKFull (k n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → k ≤ n.factorization p

/-- Alternative definition: n is k-full iff all prime factors have multiplicity ≥ k. -/
def IsKFull' (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, k ≤ n.factorization p

/-- 2-full numbers are also called **powerful** numbers. -/
def IsPowerful (n : ℕ) : Prop := IsKFull 2 n

/-- 3-full numbers are called **cubeful** numbers. -/
def IsCubeful (n : ℕ) : Prop := IsKFull 3 n

/-
## Basic Properties of k-Full Numbers
-/

/-- 1 is vacuously k-full for any k (no prime factors). -/
theorem one_is_kfull (k : ℕ) : IsKFull k 1 := by
  intro p hp hdiv
  -- p | 1 implies p = 1, but p is prime so p ≥ 2, contradiction
  have h1 : p = 1 := Nat.dvd_one.mp hdiv
  exact absurd h1 (Nat.Prime.ne_one hp)

/-
## Examples of k-Full Numbers
-/

/-- 8 = 2³ is 3-full (cubeful). -/
axiom eight_is_cubeful : IsCubeful 8

/-- 9 = 3² is 2-full (powerful). -/
axiom nine_is_powerful : IsPowerful 9

/-
## The Main Question: 2-Full n with 3-Full n+1

Erdős asked whether there exists any n such that:
- n is 2-full (powerful)
- n+1 is 3-full (cubeful)

This remains OPEN as of 2024.
-/

/-- **Erdős Problem #366**: Does there exist n > 0 such that
n is 2-full and n+1 is 3-full? -/
def erdos_366_conjecture : Prop :=
  ∃ n > 0, IsPowerful n ∧ IsCubeful (n + 1)

/-
## The Reverse Direction: 3-Full n with 2-Full n+1

The reverse direction has known solutions!
-/

/-- The set of pairs (n, n+1) where n is 3-full and n+1 is 2-full. -/
def CubefulPowerfulPairs : Set ℕ := { n | IsCubeful n ∧ IsPowerful (n + 1) }

/-- (8, 9) is a cubeful-powerful pair: 8 = 2³ is cubeful, 9 = 3² is powerful. -/
theorem eight_nine_pair : 8 ∈ CubefulPowerfulPairs := ⟨eight_is_cubeful, nine_is_powerful⟩

/-- 12167 = 23³ is cubeful. -/
axiom cubeful_12167 : IsCubeful 12167

/-- 12168 = 2³ × 3² × 13² is powerful. -/
axiom powerful_12168 : IsPowerful 12168

/-- (12167, 12168) is a cubeful-powerful pair (Golomb 1970). -/
theorem golomb_pair : 12167 ∈ CubefulPowerfulPairs :=
  ⟨cubeful_12167, powerful_12168⟩

/-
## Connection to Powerful Numbers and Pell Equations

Erdős originally asked Mahler about consecutive powerful numbers.
Mahler immediately showed infinitely many exist via Pell equations.
-/

/-- 8 = 2³ has 2 appearing with multiplicity 3 ≥ 2, so 8 is powerful. -/
axiom eight_is_powerful : IsPowerful 8

/-- 8 and 9 are consecutive powerful numbers. -/
theorem eight_nine_powerful : IsPowerful 8 ∧ IsPowerful 9 :=
  ⟨eight_is_powerful, nine_is_powerful⟩

/-
## Summary

Erdős Problem #366 asks about consecutive integers with prescribed fullness:
- (n powerful, n+1 cubeful): OPEN, no known examples
- (n cubeful, n+1 powerful): Known examples: (8,9), (12167, 12168)
- (n cubeful, n+1 cubeful): OPEN, no known examples

The sparsity of k-full numbers makes these questions difficult.
-/

end Erdos366
