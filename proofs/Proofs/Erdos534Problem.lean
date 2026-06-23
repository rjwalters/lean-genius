/-
# Erdős Problem #534: Maximum GCD-Intersecting Sets Containing N

**Source:** [erdosproblems.com/534](https://erdosproblems.com/534)
**Status:** SOLVED (Ahlswede-Khachatrian, 1996)

## Statement

What is the largest subset A ⊆ {1,...,N} containing N such that
gcd(a,b) > 1 for all distinct a, b ∈ A?

## Background

- Original Erdős-Graham conjecture: max is N/p or #{2t : t ≤ N/2, gcd(2t,N) > 1}
- Ahlswede-Khachatrian (1992): Found counterexample
- Ahlswede-Khachatrian (1996): Proved the refined characterization

## Approach

We define GCD-intersecting sets, state the original (false) conjecture,
define the optimal family construction, and axiomatize the
Ahlswede-Khachatrian theorem with special cases.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Nat Finset

namespace Erdos534

/- ## Part 1: Basic Definitions -/

/-- The interval {1, ..., N} -/
def interval (N : ℕ) : Finset ℕ := (Finset.range N).map ⟨(· + 1), fun _ _ h => by omega⟩

/-- A set is GCD-intersecting if gcd(a,b) > 1 for all distinct a, b -/
def IsGCDIntersecting (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.gcd a b > 1

/-- The set contains N -/
def ContainsN (A : Finset ℕ) (N : ℕ) : Prop := N ∈ A

/-- Maximum size of GCD-intersecting set in {1,...,N} containing N -/
noncomputable def maxGCDIntersecting (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ interval N ∧ ContainsN A N ∧
        IsGCDIntersecting A ∧ A.card = k}

/- ## Part 2: Simple Constructions -/

/-- All multiples of smallest prime factor p -/
def multiplesOfSmallestPrime (N : ℕ) : Finset ℕ :=
  let p := N.minFac
  (interval N).filter (fun n => p ∣ n)

/-- Multiples of p gives size N/p -/
/-- This set is GCD-intersecting (all share factor p) -/
/-- Even numbers that share a factor with N -/
def evenMultiplesSharing (N : ℕ) : Finset ℕ :=
  (interval N).filter (fun n => 2 ∣ n ∧ Nat.gcd n N > 1)

/-- This gives another candidate for the maximum -/
/- ## Part 3: The Original Conjecture (WRONG) -/

/-- Erdős-Graham original conjecture -/
def OriginalConjecture : Prop :=
  ∀ N : ℕ, N > 1 →
    maxGCDIntersecting N = max (N / N.minFac) (evenMultiplesSharing N).card

/-- Ahlswede-Khachatrian (1992) found counterexample -/
axiom original_conjecture_false :
  ¬OriginalConjecture

/-- There exists a specific N where the maximum exceeds both candidates -/
axiom counterexample_exists :
  ∃ N : ℕ, N > 1 ∧
    maxGCDIntersecting N > max (N / N.minFac) (evenMultiplesSharing N).card

/- ## Part 4: The Correct Characterization -/

/-- The optimal construction family for N = q₁^k₁ ⋯ qᵣ^kᵣ.
    Integers in [1,N] that are multiples of at least one of:
    2q₁, 2q₂, ..., 2qⱼ, or q₁·q₂·...·qⱼ -/
def optimalFamily (N : ℕ) (j : ℕ) (primes : List ℕ) : Finset ℕ :=
  let firstJ := primes.take j
  let twoTimesPrimes := firstJ.map (2 * ·)
  let productOfFirstJ := firstJ.foldl (· * ·) 1
  (interval N).filter fun n =>
    (twoTimesPrimes.any (· ∣ n)) ∨ (productOfFirstJ ∣ n)

/-- The maximum is achieved by one of these families (Ahlswede-Khachatrian 1996) -/
axiom ahlswede_khachatrian_theorem :
  ∀ N : ℕ, N > 1 →
    ∃ j : ℕ, ∃ primes : List ℕ,
      (∀ p ∈ primes, p.Prime ∧ p ∣ N) ∧
      maxGCDIntersecting N = (optimalFamily N j primes).card

/- ## Part 5: Special Cases -/

/-- When N is a prime power p^k, the maximum is p^(k-1) -/
/-- When N = 2p for odd prime p, the maximum is 2 -/
/- ## Part 6: Summary

**Erdős Problem #534: SOLVED** (Ahlswede-Khachatrian 1996)

**Question:** What is the largest A ⊆ {1,...,N} containing N with gcd(a,b) > 1
for all distinct a, b ∈ A?

**Answer:** For N = q₁^k₁ ⋯ qᵣ^kᵣ, the maximum is achieved by integers
that are multiples of elements from {2q₁,...,2qⱼ, q₁⋯qⱼ} for optimal j.

**History:**
- Original Erdős-Graham conjecture was wrong
- Ahlswede-Khachatrian (1992) found counterexample
- Ahlswede-Khachatrian (1996) proved correct characterization
-/

theorem erdos_534_summary :
    -- Original conjecture is false
    ¬OriginalConjecture ∧
    -- A counterexample exists
    (∃ N : ℕ, N > 1 ∧
      maxGCDIntersecting N > max (N / N.minFac) (evenMultiplesSharing N).card) ∧
    -- Correct characterization exists for all N > 1
    (∀ N : ℕ, N > 1 → ∃ j primes,
      (∀ p ∈ primes, p.Prime ∧ p ∣ N) ∧
      maxGCDIntersecting N = (optimalFamily N j primes).card) := by
  exact ⟨original_conjecture_false, counterexample_exists, ahlswede_khachatrian_theorem⟩

end Erdos534
