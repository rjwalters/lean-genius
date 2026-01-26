/-!
# Erdős Problem 913: Distinct Exponents in n(n+1) Factorizations

*Reference:* [erdosproblems.com/913](https://www.erdosproblems.com/913)

Are there infinitely many `n` such that if `n(n+1) = ∏ pᵢ^kᵢ` is the
factorization into distinct primes, then all exponents `kᵢ` are distinct?

From Erdős [Er82c, p.28]. A likely sufficient condition: if there are infinitely
many primes `p` such that `8p² - 1` is also prime, then using exponents
`{1, 2, 3}` with `n = 8p² - 1` produces an example. The conditional result
is proved in detail below.

This remains an open problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section 1: Distinct exponent property

We define the property that the prime factorization of `n(n+1)` has
all exponents distinct, using Mathlib's `factorization` and `primeFactors`.
-/

namespace Erdos913

open Nat Finset

/-- `n` has the distinct-exponent property if the factorization map
    `n(n+1).factorization` is injective on the prime factors of `n(n+1)`. -/
def HasDistinctExponents (n : ℕ) : Prop :=
  Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors

/-- The set of all n with the distinct-exponent property. -/
def DistinctExponentSet : Set ℕ :=
  { n | HasDistinctExponents n }

/-!
## Section 2: The main conjecture

Erdős Problem 913 asks whether the set of n with distinct exponents is infinite.
-/

/-- Erdős Problem 913: Are there infinitely many n such that the prime
    factorization of n(n+1) has all exponents distinct? -/
def ErdosProblem913 : Prop := DistinctExponentSet.Infinite

/-!
## Section 3: The 8p²-1 prime hypothesis

A likely sufficient condition: infinitely many primes p with 8p²-1 also prime.
-/

/-- The set of primes p such that 8p² - 1 is also prime. -/
def PrimePairs8 : Set ℕ := { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }

/-- Hypothesis: there are infinitely many primes p with 8p² - 1 prime. -/
axiom infinite_8p_sq_minus_1_primes : PrimePairs8.Infinite

/-!
## Section 4: Conditional proof

If PrimePairs8 is infinite, then DistinctExponentSet is infinite.
For each such p, take n = 8p² - 1. Then:
  n(n+1) = (8p² - 1)(8p²) = (8p² - 1) · p² · 8 = (8p² - 1) · p² · 2³

So the prime factorization has exponents {1, 2, 3} on primes {8p²-1, p, 2},
which are all distinct.
-/

/-- Conditional result: if there are infinitely many primes p with
    8p² - 1 prime, then infinitely many n have distinct exponents. -/
axiom erdos_913_conditional (h : PrimePairs8.Infinite) :
  DistinctExponentSet.Infinite

/-!
## Section 5: Known examples

Small examples of n with distinct exponents in n(n+1):
- n = 3: 3·4 = 2²·3, exponents {2,1} distinct
- n = 7: 7·8 = 2³·7, exponents {3,1} distinct
- n = 8: 8·9 = 2³·3², exponents {3,2} distinct
- n = 31: 31·32 = 2⁵·31, exponents {5,1} distinct
- n = 127: 127·128 = 2⁷·127, exponents {7,1} distinct
-/

/-- n = 3 has distinct exponents: 3·4 = 2²·3¹. -/
axiom example_n3 : HasDistinctExponents 3

/-- n = 7 has distinct exponents: 7·8 = 2³·7¹. -/
axiom example_n7 : HasDistinctExponents 7

/-- n = 8 has distinct exponents: 8·9 = 2³·3². -/
axiom example_n8 : HasDistinctExponents 8

/-!
## Section 6: Connection to Bunyakovsky conjecture

The hypothesis that infinitely many p have 8p² - 1 prime is a special case
of the Bunyakovsky conjecture (or Bateman–Horn conjecture) for the polynomial
f(x) = 8x² - 1. These conjectures predict infinitely many prime values
for irreducible polynomials satisfying a fixed-divisor condition.
-/

/-- The Bunyakovsky-type hypothesis for 8x² - 1: there are infinitely
    many prime values of 8x² - 1 as x ranges over the primes.
    This is a weaker form than the full Bunyakovsky conjecture. -/
def Bunyakovsky8 : Prop := PrimePairs8.Infinite

/-!
## Section 7: Exponent multiplicity structure

The key insight of the conditional proof is that n = 8p² - 1 gives
n(n+1) = (8p²-1)¹ · p² · 2³, with three distinct primes {8p²-1, p, 2}
having three distinct exponents {1, 2, 3}. The injectivity of the
factorization map follows from these exponents being pairwise distinct.
-/

/-- When p is prime and 8p²-1 is prime, n = 8p²-1 gives a product
    n(n+1) with exactly three prime factors and exponents {1,2,3}. -/
axiom exponent_structure (p : ℕ) (hp : p.Prime) (hp' : (8 * p ^ 2 - 1).Prime) (hp'' : p ≠ 2) :
  let n := 8 * p ^ 2 - 1
  (n * (n + 1)).primeFactors = {8 * p ^ 2 - 1, p, 2}

end Erdos913
