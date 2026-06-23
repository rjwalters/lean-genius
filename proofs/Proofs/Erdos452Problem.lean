/-
# Erdős Problem #452: Largest Interval with ω(n) > log log n

Source: https://erdosproblems.com/452
Status: OPEN

Statement:
Let ω(n) count the number of distinct prime factors of n.
What is the size of the largest interval I ⊆ [x, 2x] such that
ω(n) > log log n for all n ∈ I?

Known Results:
- Erdős (1937): The density of integers with ω(n) > log log n is 1/2
- Chinese Remainder Theorem implies |I| ≥ (1+o(1)) log x / (log log x)²
- Conjecture: There exists such an interval of length (log x)^k for any k

Background:
- ω(n) is the number of distinct prime divisors (e.g., ω(12) = 2 for primes 2, 3)
- The Hardy-Ramanujan theorem: ω(n) ≈ log log n for most n
- Erdős-Kac theorem: (ω(n) - log log n) / √(log log n) → Normal(0,1)

Tags: number-theory, prime-factors, analytic-number-theory
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos452

open Nat ArithmeticFunction Real

/-
## Part 1: Basic Definitions

The number of distinct prime factors ω(n).
-/

/-- The number of distinct prime factors of n -/
def omega (n : ℕ) : ℕ := (n.primeFactors).card

/-- Alternative: using Mathlib's cardDistinctFactors -/
def omega' (n : ℕ) : ℕ := n.primeFactors.card

/-- An integer n satisfies the condition ω(n) > log log n -/
def satisfiesCondition (n : ℕ) : Prop :=
  (omega n : ℝ) > Real.log (Real.log n)

/-- An interval I ⊆ [x, 2x] where all elements satisfy the condition -/
def validInterval (x : ℕ) (a b : ℕ) : Prop :=
  x ≤ a ∧ b ≤ 2 * x ∧ a ≤ b ∧
  ∀ n, a ≤ n → n ≤ b → satisfiesCondition n

/-- The length of an interval -/
def intervalLength (a b : ℕ) : ℕ := b - a + 1

/-
## Part 2: Hardy-Ramanujan and Erdős-Kac

The normal order of ω(n) is log log n.
-/

/-- Erdős (1937): The density of n with ω(n) > log log n is exactly 1/2 -/
axiom erdos_1937_density :
    ∀ ε > 0, ∃ N : ℕ, ∀ x ≥ N,
      |(({n ∈ Finset.Icc 1 x | satisfiesCondition n}.card : ℝ) / x - 1/2)| < ε

/-
## Part 3: Lower Bound via Chinese Remainder Theorem

The CRT gives a construction of valid intervals.
-/

/-
## Part 4: The Main Question

What is the maximum length of such an interval?
-/

/-- The maximum length of a valid interval in [x, 2x] -/
axiom maxValidIntervalLength (x : ℕ) : ℕ

/-
## Part 5: Upper Bounds

What limits the length of valid intervals?
-/

/-- Prime gaps give some limitations -/
axiom prime_gap_constraint :
    ∀ x : ℕ, x ≥ 16 → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ p ≤ 2*x ∧ ¬satisfiesCondition p

/-
## Part 6: Primorial Connection

The primorial n# has many prime factors.
-/

/-- The primorial: product of all primes ≤ n -/
noncomputable def primorial (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).prod id

/-
## Part 7: Small Examples
-/

/-- ω(1) = 0 -/
example : omega 1 = 0 := by
  simp only [omega, Nat.primeFactors_one, Finset.card_empty]

/-- ω(2) = 1 -/
example : omega 2 = 1 := by native_decide

/-- ω(6) = 2 (primes 2 and 3) -/
example : omega 6 = 2 := by native_decide

/-- ω(30) = 3 (primes 2, 3, 5) -/
example : omega 30 = 3 := by native_decide

/-- ω(210) = 4 (primes 2, 3, 5, 7) -/
example : omega 210 = 4 := by native_decide

/-
## Part 8: Consecutive Integers with Many Prime Factors
-/

/-
## Part 9: Related Problems
-/

/-- Ω(n): count prime factors with multiplicity -/
def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Similar question for Ω instead of ω -/
def bigOmegaCondition (n : ℕ) : Prop :=
  (bigOmega n : ℝ) > Real.log (Real.log n)

/-- The radical rad(n) = product of distinct prime factors -/
noncomputable def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/-
## Part 10: Current State of Knowledge

The problem remains open.
-/

/-- Known: Lower bound (log x)/(log log x)² -/
axiom known_lower_bound (x : ℕ) (hx : x ≥ 3) :
    ∃ a b : ℕ, validInterval x a b ∧
      (intervalLength a b : ℝ) ≥ Real.log x / (Real.log (Real.log x))^2

/-
## Part 11: Summary

Erdős Problem #452 is OPEN.
-/

/-- Summary of Erdős Problem #452:
    1. Density of {n : ω(n) > log log n} is 1/2 (Erdős 1937)
    2. CRT gives valid intervals of length ≥ log x / (log log x)²
    3. Primes obstruct: valid intervals cannot contain primes > 16
    4. Open conjecture: intervals of length (log x)^k should exist for any k -/
theorem erdos_452_summary :
    -- Density result exists
    (∀ ε > 0, ∃ N : ℕ, ∀ x ≥ N,
      |(({n ∈ Finset.Icc 1 x | satisfiesCondition n}.card : ℝ) / x - 1/2)| < ε) ∧
    -- CRT lower bound exists
    (∀ x : ℕ, x ≥ 3 → ∃ a b : ℕ, validInterval x a b ∧
      (intervalLength a b : ℝ) ≥ Real.log x / (Real.log (Real.log x))^2) ∧
    -- Primes fail the condition
    (∀ x : ℕ, x ≥ 16 → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ p ≤ 2*x ∧ ¬satisfiesCondition p) :=
  ⟨erdos_1937_density, known_lower_bound, prime_gap_constraint⟩

end Erdos452
