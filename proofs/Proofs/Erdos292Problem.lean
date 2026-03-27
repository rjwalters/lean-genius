/-
Erdős Problem #292: Egyptian Fractions Summing to 1

Source: https://erdosproblems.com/292
Status: SOLVED (Martin 2000)

Statement:
Let A be the set of n ∈ ℕ such that there exist 1 ≤ m₁ < ... < mₖ = n with
Σ(1/mᵢ) = 1. Does A have density 1?

Answer: YES (Martin 2000)

Background:
Egyptian fractions are sums of distinct unit fractions. This problem asks
which integers can appear as the largest denominator in an Egyptian fraction
representation of 1.

Known Results:
- Straus: A is closed under multiplication
- A does not contain any prime power
- If n ∈ A (n > 1), then 2n ∈ A
- Martin (2000): A has density 1; complement B = ℕ\A has density ~(log log x)/(log x)

References:
- [Ma00] Martin, "Dense Egyptian fractions"

Tags: number-theory, egyptian-fractions, density, unit-fractions
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Erdos292

/-
## Part 1: Egyptian Fractions
-/

/-- An Egyptian fraction representation of r is a finite set of distinct
    positive integers whose reciprocals sum to r -/
def EgyptianFraction (S : Finset ℕ) (r : ℚ) : Prop :=
  (∀ m ∈ S, m ≥ 1) ∧
  (S.sum (fun m => (1 : ℚ) / m)) = r

/-- The set A: integers that can be the largest denominator in an
    Egyptian fraction summing to 1 -/
def setA : Set ℕ :=
  { n : ℕ | ∃ S : Finset ℕ, n ∈ S ∧ (∀ m ∈ S, m ≤ n) ∧
    EgyptianFraction S 1 }

/-- Alternative definition: n ∈ A iff there exist 1 ≤ m₁ < ... < mₖ = n
    with Σ(1/mᵢ) = 1 -/
def inSetA (n : ℕ) : Prop :=
  ∃ (k : ℕ) (m : Fin k → ℕ),
    (∀ i j, i < j → m i < m j) ∧
    (∃ i, m i = n) ∧
    (∀ i, m i ≥ 1) ∧
    (Finset.univ.sum (fun i => (1 : ℚ) / (m i))) = 1

/-
## Part 2: Basic Properties
-/

/-
## Part 3: Straus's Observation - Closure Under Multiplication
-/

/-- Straus's Theorem: A is closed under multiplication -/
axiom straus_multiplication_closure :
  ∀ n m : ℕ, n ∈ setA → m ∈ setA → n * m ∈ setA

/-- Corollary: If n ∈ A then all multiples n·k (with k ∈ A) are in A -/
theorem multiples_in_A (n : ℕ) (hn : n ∈ setA) :
    ∀ k ∈ setA, n * k ∈ setA := by
  intro k hk
  exact straus_multiplication_closure n k hn hk

/-
## Part 4: Prime Powers are Not in A
-/

/-- Prime powers are not in A -/
axiom prime_powers_not_in_A :
  ∀ p : ℕ, Nat.Prime p → ∀ k : ℕ, k ≥ 1 → p^k ∉ setA

/-- Specific case: 2 ∉ A -/
theorem two_not_in_A : 2 ∉ setA := by
  have : Nat.Prime 2 := Nat.prime_two
  exact prime_powers_not_in_A 2 this 1 (by norm_num)

/-- Specific case: 4 ∉ A -/
theorem four_not_in_A : 4 ∉ setA := by
  have h4 : 4 = 2^2 := by norm_num
  rw [h4]
  exact prime_powers_not_in_A 2 Nat.prime_two 2 (by norm_num)

/-- All primes are not in A -/
theorem primes_not_in_A (p : ℕ) (hp : Nat.Prime p) : p ∉ setA := by
  have : p = p^1 := by ring
  rw [this]
  exact prime_powers_not_in_A p hp 1 (by norm_num)

/-
## Part 5: Doubling Property
-/

/-
## Part 6: The Complement Set B
-/

/-- The complement B = ℕ \ A -/
def setB : Set ℕ := setA.compl

/-
## Part 7: Martin's Main Theorem
-/

/-- Natural density definition -/
def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun n => (Finset.filter (· ∈ S) (Finset.range n)).card / (n : ℝ))
    Filter.atTop (nhds d)

/-- Martin's Main Theorem: A has density 1 -/
axiom martin_main_theorem : hasNaturalDensity setA 1

/-
## Part 8: Small Examples Analysis
-/

/-
## Part 9: Connections to Other Problems
-/

/-- Egyptian fraction problem (Erdős-Straus): 4/n = 1/a + 1/b + 1/c -/
def erdosStrausConjecture : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∃ a b c : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧
    (4 : ℚ) / n = 1/a + 1/b + 1/c

/-
## Part 10: Summary
-/

/-- Main Result: Erdős Problem #292 is SOLVED -/
theorem erdos_292 : hasNaturalDensity setA 1 := martin_main_theorem

end Erdos292
