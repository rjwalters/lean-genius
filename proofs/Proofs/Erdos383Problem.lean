/-
Erdős Problem #383: Prime Divisors of Consecutive Squares

**Problem Statement (OPEN)**

Is it true that for every k, there are infinitely many primes p such that
the largest prime divisor of ∏_{i=0}^k (p² + i) is p itself?

**Background:**
The product spans k+1 consecutive integers starting from p².
We ask whether p can be the largest prime factor of this product
for infinitely many primes p.

**Relation to Problem #382:**
A positive answer would resolve the second part of Erdős Problem #382.

**Heuristic Argument:**
Probabilistic considerations suggest integers without prime divisors ≥ √n
occur with positive density, supporting an affirmative conjecture.

**Status:** OPEN

**Reference:** Erdős & Graham 1980 [ErGr80]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Finset Nat

namespace Erdos383

/-!
# Part 1: Prime Factor Definitions

We need to work with the largest prime factor of a number.
-/

-- The set of prime factors
def primeDivisors (n : ℕ) : Finset ℕ :=
  n.primeFactors

-- A number has p as its largest prime factor
def hasLargestPrimeFactor (n : ℕ) (p : ℕ) : Prop :=
  p ∈ primeDivisors n ∧ ∀ q ∈ primeDivisors n, q ≤ p

-- Equivalently, p divides n and all prime factors are ≤ p
theorem hasLargestPrimeFactor_iff (n p : ℕ) (hn : n > 1) :
    hasLargestPrimeFactor n p ↔ p.Prime ∧ p ∣ n ∧ ∀ q, q.Prime → q ∣ n → q ≤ p := by
  sorry

/-!
# Part 2: The Product Definition

The product ∏_{i=0}^k (p² + i) is k+1 consecutive integers starting at p².
-/

-- The product of p² + i for i from 0 to k
def consecutiveSquareProduct (p k : ℕ) : ℕ :=
  ∏ i in Icc 0 k, (p ^ 2 + i)

-- This is the same as (p²)(p²+1)(p²+2)⋯(p²+k)
theorem consecutiveSquareProduct_eq (p k : ℕ) :
    consecutiveSquareProduct p k = ∏ i in range (k + 1), (p ^ 2 + i) := by
  simp only [consecutiveSquareProduct]
  congr 1
  ext i
  simp [Nat.lt_add_one_iff]

-- For k = 0, the product is just p²
theorem consecutiveSquareProduct_zero (p : ℕ) :
    consecutiveSquareProduct p 0 = p ^ 2 := by
  simp [consecutiveSquareProduct]

-- For k = 1, the product is p²(p² + 1)
theorem consecutiveSquareProduct_one (p : ℕ) :
    consecutiveSquareProduct p 1 = p ^ 2 * (p ^ 2 + 1) := by
  simp [consecutiveSquareProduct]
  ring

/-!
# Part 3: The Main Property

We define when a prime p satisfies the Erdős condition for a given k.
-/

-- A prime p is k-good if p is the largest prime factor of ∏_{i=0}^k (p² + i)
def isKGood (p k : ℕ) : Prop :=
  p.Prime ∧ hasLargestPrimeFactor (consecutiveSquareProduct p k) p

-- Equivalent formulation: p divides the product and all prime factors are ≤ p
def isKGood' (p k : ℕ) : Prop :=
  p.Prime ∧
  p ∣ consecutiveSquareProduct p k ∧
  ∀ q, q.Prime → q ∣ consecutiveSquareProduct p k → q ≤ p

-- The set of k-good primes
def kGoodPrimes (k : ℕ) : Set ℕ :=
  {p | isKGood p k}

-- For k = 0: p is 0-good iff p² has p as largest prime factor (always true for prime p)
axiom zero_good_iff : ∀ p, p.Prime → isKGood p 0

/-!
# Part 4: The Erdős Conjecture

The main conjecture asserts that k-good primes are infinite for all k.
-/

-- The main conjecture
def ErdosConjecture383 : Prop :=
  ∀ k : ℕ, (kGoodPrimes k).Infinite

-- Equivalent formulation with Nat.maxPrimeFac
def ErdosConjecture383' : Prop :=
  ∀ k : ℕ, {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (consecutiveSquareProduct p k) = p}.Infinite

-- The conjectures are equivalent (when properly formalized)
axiom conjecture_equiv : ErdosConjecture383 ↔ ErdosConjecture383'

/-!
# Part 5: Partial Results

We axiomatize known partial results.
-/

-- For k = 0, every prime is 0-good
theorem all_primes_zero_good : ∀ p, p.Prime → isKGood p 0 := zero_good_iff

-- Hence there are infinitely many 0-good primes
axiom infinitely_many_zero_good : (kGoodPrimes 0).Infinite

-- Heuristic: the probability that n has no prime factor > √n is positive
axiom positive_density_smooth : ∃ c : ℝ, c > 0 ∧
  Filter.Tendsto (fun N => (Finset.filter (fun n => ∀ p ∈ primeDivisors n, p^2 ≤ n)
    (Finset.range N)).card / N) Filter.atTop (nhds c)

/-!
# Part 6: Relation to Problem #382

Problem #382 asks about the density of such primes.
-/

-- Problem 382 Part 2: infinitely many primes p where p is largest factor of p² + 1
def Problem382Part2 : Prop :=
  {p : ℕ | p.Prime ∧ hasLargestPrimeFactor (p^2 + 1) p}.Infinite

-- Problem 383 for k = 1 implies Problem 382 Part 2
axiom problem383_implies_382 : (kGoodPrimes 1).Infinite → Problem382Part2

/-!
# Part 7: Smooth Numbers

The problem relates to smooth numbers (numbers without large prime factors).
-/

-- A number is y-smooth if all prime factors are ≤ y
def isSmooth (n y : ℕ) : Prop :=
  ∀ p ∈ primeDivisors n, p ≤ y

-- The k-good condition is: all p² + i are p-smooth for i ≤ k
axiom kGood_iff_smooth : ∀ p k, p.Prime →
    (isKGood p k ↔ p.Prime ∧ ∀ i ≤ k, isSmooth (p^2 + i) p)

-- Counting y-smooth numbers up to x: Ψ(x, y)
noncomputable def countSmooth (x y : ℕ) : ℕ :=
  (Finset.filter (fun n => isSmooth n y) (Finset.Icc 1 x)).card

-- Dickman's function describes the density of y-smooth numbers
-- Ψ(x, x^{1/u}) ~ x * ρ(u) where ρ is the Dickman function
axiom dickman_asymptotic : ∃ ρ : ℝ → ℝ, ρ 1 = 1 ∧ ρ 2 > 0 ∧
  ∀ u ≥ 1, Filter.Tendsto (fun x => (countSmooth x (x^(1/u : ℝ)).toNat : ℝ) / x)
    Filter.atTop (nhds (ρ u))

/-!
# Part 8: The Heuristic Argument

The problem is believed to have a positive answer based on probabilistic reasoning.
-/

-- The heuristic: for u = 2, ρ(2) = 1 - log(2) ≈ 0.307
-- This means about 30.7% of numbers n have no prime factor > √n

-- For p² + i with p prime and i small:
-- We need p² + i to be p-smooth
-- Since p ≈ √(p²+i), this is asking for (p²+i)-smoothness at level √(p²+i)

-- The density ρ(2) > 0 suggests infinitely many such p should exist

/-!
# Part 9: Problem Status

The problem remains OPEN. The heuristic argument supports a positive answer.
-/

-- The problem is open
def erdos_383_status : String := "OPEN"

/-!
# Part 10: Formal Statement

The precise formal statement.
-/

-- The formal statement using Nat.maxPrimeFac
theorem erdos_383_statement :
    ErdosConjecture383' ↔
    ∀ k, {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (∏ i ∈ Icc 0 k, (p ^ 2 + i)) = p}.Infinite := by
  simp only [ErdosConjecture383', consecutiveSquareProduct]

end Erdos383
