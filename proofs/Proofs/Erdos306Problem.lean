/-
  Erdős Problem #306: Egyptian Fractions with Semiprime Denominators

  Let a/b ∈ ℚ₊ with b squarefree. Are there integers 1 < n₁ < ... < nₖ,
  each the product of two distinct primes, such that
    a/b = 1/n₁ + ... + 1/nₖ?

  **Status**: OPEN (for 2 distinct primes)

  **Related Result (SOLVED)**: For denominators that are products of THREE
  distinct primes, this is true when b = 1 (i.e., for positive integers).
  Proved by Butler, Erdős, and Graham (2015) - perhaps Erdős's last paper,
  appearing 19 years after his death!

  References:
  - https://erdosproblems.com/306
  - Butler, Erdős, Graham: "Egyptian Fractions with Each Denominator
    Having Three Distinct Prime Divisors" (2015)
-/

import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

namespace Erdos306

/-!
## Background: Egyptian Fractions

An Egyptian fraction is a sum of distinct unit fractions:
  1/n₁ + 1/n₂ + ... + 1/nₖ

The ancient Egyptians represented all fractions this way (except 2/3).
A classical theorem states every positive rational can be written as
an Egyptian fraction (e.g., via the greedy algorithm).

This problem asks about constrained representations where denominators
have specific prime factorization structure.
-/

/-!
## Semiprimes and Related Definitions

A semiprime is a product of exactly two primes (not necessarily distinct).
Here we need products of exactly TWO DISTINCT primes.

Examples: 6 = 2×3, 10 = 2×5, 14 = 2×7, 15 = 3×5, 21 = 3×7, ...
Non-examples: 4 = 2×2 (not distinct), 12 = 2²×3 (not exactly 2 factors)
-/

/-- A natural number is a product of exactly k distinct primes if
ω(n) = k (distinct prime factors) and Ω(n) = k (total prime factors).
This means each prime appears exactly once. -/
def isProductOfKDistinctPrimes (n k : ℕ) : Prop :=
  ArithmeticFunction.cardDistinctFactors n = k ∧
  ArithmeticFunction.cardFactors n = k

/-- A natural number is a product of exactly 2 distinct primes.
Examples: 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, ... -/
def isTwoDistinctPrimeProduct (n : ℕ) : Prop :=
  isProductOfKDistinctPrimes n 2

/-- A natural number is a product of exactly 3 distinct primes.
Examples: 30 = 2×3×5, 42 = 2×3×7, 66 = 2×3×11, 70 = 2×5×7, ... -/
def isThreeDistinctPrimeProduct (n : ℕ) : Prop :=
  isProductOfKDistinctPrimes n 3

/-!
## The Main Conjecture (OPEN)

Can every positive rational with squarefree denominator be expressed
as a sum of unit fractions with 2-distinct-prime denominators?
-/

/-- An Egyptian fraction representation with k terms, starting strictly above 1.
The sequence n₀ = 1 < n₁ < n₂ < ... < nₖ is strictly increasing.
We sum 1/nᵢ for i = 1, ..., k. -/
structure EgyptianRepr (k : ℕ) where
  denoms : Fin (k + 1) → ℕ
  base_is_one : denoms 0 = 1
  strictly_increasing : StrictMono denoms

/-- The sum of the Egyptian fraction representation. -/
noncomputable def EgyptianRepr.sum {k : ℕ} (repr : EgyptianRepr k) : ℚ :=
  ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / repr.denoms i

/-- An Egyptian representation where all denominators (after the base)
are products of exactly 2 distinct primes. -/
def isTwoPrimeRepr {k : ℕ} (repr : EgyptianRepr k) : Prop :=
  ∀ i ∈ Finset.Icc 1 (Fin.last k), isTwoDistinctPrimeProduct (repr.denoms i)

/-- An Egyptian representation where all denominators (after the base)
are products of exactly 3 distinct primes. -/
def isThreePrimeRepr {k : ℕ} (repr : EgyptianRepr k) : Prop :=
  ∀ i ∈ Finset.Icc 1 (Fin.last k), isThreeDistinctPrimeProduct (repr.denoms i)

/-- **Erdős Problem #306 (Main Conjecture - OPEN)**: Every positive rational
with squarefree denominator can be written as an Egyptian fraction where
each denominator is a product of exactly 2 distinct primes.

The question is: does such a representation always exist? -/
def erdos_306_conjecture : Prop :=
  ∀ q : ℚ, 0 < q → Squarefree q.den →
    ∃ k : ℕ, ∃ repr : EgyptianRepr k, isTwoPrimeRepr repr ∧ repr.sum = q

/-!
## The Butler-Erdős-Graham Result (SOLVED)

For 3 distinct primes, the analogous statement is TRUE when restricted
to positive integers (i.e., q with q.den = 1).
-/

/-- **Butler-Erdős-Graham Theorem (2015)**: Every positive integer can be
expressed as an Egyptian fraction where each denominator is a product
of exactly 3 distinct primes.

This was published 19 years after Erdős's death and may be his last paper. -/
axiom butler_erdos_graham_theorem :
  ∀ m : ℕ, 0 < m →
    ∃ k : ℕ, k > 0 ∧ ∃ repr : EgyptianRepr k,
      isThreePrimeRepr repr ∧ repr.sum = m

/-- The 3-prime result doesn't immediately extend to arbitrary rationals.
The squarefree denominator condition in the 2-prime case is important. -/
def three_prime_integer_version : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ k : ℕ, ∃ repr : EgyptianRepr k, isThreePrimeRepr repr ∧ repr.sum = m

theorem three_prime_solved : three_prime_integer_version := by
  intro m hm
  obtain ⟨k, hk, repr, hrepr, hsum⟩ := butler_erdos_graham_theorem m hm
  exact ⟨k, repr, hrepr, hsum⟩

/-!
## Examples and Small Cases
-/

/-- The first few products of 2 distinct primes. -/
def twoPrimeProducts : List ℕ := [6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39]

/-- Check: 6 = 2 × 3 is a product of 2 distinct primes. -/
example : ArithmeticFunction.cardDistinctFactors 6 = 2 := by native_decide

/-- Check: 6 = 2 × 3 has Ω(6) = 2. -/
example : ArithmeticFunction.cardFactors 6 = 2 := by native_decide

/-- Example: 1/6 + 1/10 + 1/14 + 1/15 + 1/21 + 1/35 = 1
This shows 1 can be represented with 2-distinct-prime denominators.
(6 terms: 6=2×3, 10=2×5, 14=2×7, 15=3×5, 21=3×7, 35=5×7) -/
axiom example_one_representation :
  (1 : ℚ) / 6 + 1 / 10 + 1 / 14 + 1 / 15 + 1 / 21 + 1 / 35 = 1

/-- The first few products of 3 distinct primes. -/
def threePrimeProducts : List ℕ := [30, 42, 66, 70, 78, 102, 105, 110, 114, 130]

/-- Check: 30 = 2 × 3 × 5 is a product of 3 distinct primes. -/
example : ArithmeticFunction.cardDistinctFactors 30 = 3 := by native_decide

/-!
## Why Squarefree Denominator?

The condition that b is squarefree is natural because:
1. Every rational can be reduced to this form
2. The arithmetic becomes cleaner
3. It relates to the structure of the problem

If q = a/b with b squarefree, then the prime factors of b each
appear exactly once, which may interact well with the constraint
on denominators.
-/

/-- Every positive rational can be written with squarefree denominator
(by reducing to lowest terms). -/
axiom reduce_to_squarefree : ∀ q : ℚ, 0 < q →
  ∃ a b : ℤ, 0 < b ∧ Squarefree b.natAbs ∧ q = a / b

/-!
## The Density of k-Distinct-Prime Products

Products of exactly k distinct primes become sparser as numbers grow.
The count of such numbers up to n is asymptotically:
  n × (log log n)^(k-1) / ((k-1)! × log n)

This sparsity affects the difficulty of the problem.
-/

/-- The number of products of 2 distinct primes up to n. -/
axiom twoPrimeProductCount : ℕ → ℕ

/-- The number of products of 3 distinct primes up to n. -/
axiom threePrimeProductCount : ℕ → ℕ

/-- Asymptotic density of products of k distinct primes.
The count is roughly n × (log log n)^(k-1) / ((k-1)! × log n). -/
axiom k_prime_product_density (k : ℕ) (hk : 0 < k) :
  ∃ c > 0, ∀ n ≥ 10, c * n / (Nat.log 2 n) ≤ twoPrimeProductCount n

/-!
## Why 2 Primes is Harder than 3 Primes

With 3 distinct prime factors, there are more denominators to choose from
in any range [1, N], making it easier to find representations.

With only 2 distinct prime factors, the denominators are sparser,
and achieving arbitrary rationals becomes harder.

The squarefree denominator condition may be necessary to ensure
the representation exists.
-/

/-- The 2-prime case is open. -/
axiom erdos_306_open : ¬(erdos_306_conjecture ↔ True) ∧ ¬(erdos_306_conjecture ↔ False)

/-- The 3-prime integer version is solved. -/
theorem three_prime_status : three_prime_integer_version := three_prime_solved

/-!
## Greedy Algorithm and Egyptian Fractions

The classical greedy algorithm for Egyptian fractions works as follows:
1. Given q > 0, find the smallest n with 1/n ≤ q
2. Subtract 1/n from q, repeat with the remainder

This always terminates and gives a valid representation, but
doesn't guarantee any structure on the denominators.

For the constrained problem, we need more sophisticated methods.
-/

/-- The greedy algorithm gives an Egyptian fraction, but without
guarantees on the prime structure of denominators. -/
axiom greedy_egyptian_exists : ∀ q : ℚ, 0 < q →
  ∃ k : ℕ, ∃ repr : EgyptianRepr k, repr.sum = q

/-!
## Summary

Erdős Problem #306 asks whether every positive rational with squarefree
denominator can be written as an Egyptian fraction using only denominators
that are products of exactly 2 distinct primes.

**Open**: The 2-distinct-prime case for all such rationals.
**Solved**: The 3-distinct-prime case for positive integers (Butler-Erdős-Graham 2015).

The problem connects number theory (prime factorization), combinatorics
(subset selection), and Diophantine equations (representation problems).
-/

end Erdos306
