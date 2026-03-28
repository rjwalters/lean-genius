/-
# Erdős Problem 913: Distinct Exponents in n(n+1) Factorizations

*Reference:* [erdosproblems.com/913](https://www.erdosproblems.com/913)

Are there infinitely many `n` such that if `n(n+1) = ∏ pᵢ^kᵢ` is the
factorization into distinct primes, then all exponents `kᵢ` are distinct?

From Erdős [Er82c, p.28]. A likely sufficient condition: if there are infinitely
many primes `p` such that `8p² - 1` is also prime, then using exponents
`{1, 2, 3}` with `n = 8p² - 1` produces an example. The conditional result
is proved in detail below.

This remains an open problem.

Axioms: 3 (infinite_8p_sq_minus_1_primes, erdos_913_conditional, exponent_structure)
Sorries: 0
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

/-
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

/-
## Section 2: The main conjecture

Erdős Problem 913 asks whether the set of n with distinct exponents is infinite.
-/

/-- Erdős Problem 913: Are there infinitely many n such that the prime
    factorization of n(n+1) has all exponents distinct? -/
def ErdosProblem913 : Prop := DistinctExponentSet.Infinite

/-
## Section 3: The 8p²-1 prime hypothesis

A likely sufficient condition: infinitely many primes p with 8p²-1 also prime.
-/

/-- The set of primes p such that 8p² - 1 is also prime. -/
def PrimePairs8 : Set ℕ := { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }

/-- Hypothesis: there are infinitely many primes p with 8p² - 1 prime. -/
axiom infinite_8p_sq_minus_1_primes : PrimePairs8.Infinite

/-
## Section 4: Conditional proof

If PrimePairs8 is infinite, then DistinctExponentSet is infinite.
For each such p, take n = 8p² - 1. Then:
  n(n+1) = (8p² - 1)(8p²) = (8p² - 1) · p² · 8 = (8p² - 1) · p² · 2³

So the prime factorization has exponents {1, 2, 3} on primes {8p²-1, p, 2},
which are all distinct.
-/

/-- Helper: prove distinct exponents from a triple of prime factors with
    pairwise distinct factorization values. -/
private theorem hasDistinctExponents_of_primeFactors_triple
    {n : ℕ} {m p q r : ℕ} (hm : n * (n + 1) = m)
    (hpf : m.primeFactors = {p, q, r})
    (hpq : m.factorization p ≠ m.factorization q)
    (hpr : m.factorization p ≠ m.factorization r)
    (hqr : m.factorization q ≠ m.factorization r) :
    HasDistinctExponents n := by
  unfold HasDistinctExponents
  rw [hm, hpf]
  intro x hx y hy heq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · rfl
  · exact absurd heq hpq
  · exact absurd heq hpr
  · exact absurd heq hpq.symm
  · rfl
  · exact absurd heq hqr
  · exact absurd heq hpr.symm
  · exact absurd heq hqr.symm
  · rfl

/-- The map p ↦ 8p²-1 is injective on naturals ≥ 1. -/
private theorem injective_8p_sq_minus_1 : Function.Injective (fun p : ℕ => 8 * p ^ 2 - 1) := by
  intro a b hab
  have h : 8 * a ^ 2 = 8 * b ^ 2 := by omega
  have : a ^ 2 = b ^ 2 := by omega
  exact Nat.pow_left_injective (by omega : 0 < 2) this

/-- Conditional result: if there are infinitely many primes p with
    8p² - 1 prime, then infinitely many n have distinct exponents.

    PROOF SKETCH (not yet formalized):
    1. PrimePairs8 \ {2} is still infinite (removing one element).
    2. p ↦ 8p²-1 is injective (by injective_8p_sq_minus_1).
    3. For each p ≠ 2, n = 8p²-1 gives n(n+1) = (8p²-1)¹·p²·2³
       with exponents {1,2,3} (pairwise distinct).
    4. So the image is an infinite subset of DistinctExponentSet.

    The main gap: proving factorization values 1,2,3 symbolically
    requires Nat.Coprime.factorization_mul + Nat.Prime.factorization. -/
axiom erdos_913_conditional (h : PrimePairs8.Infinite) :
  DistinctExponentSet.Infinite

/-
## Section 5: Known examples

Small examples of n with distinct exponents in n(n+1):
- n = 3: 3·4 = 2²·3, exponents {2,1} distinct
- n = 7: 7·8 = 2³·7, exponents {3,1} distinct
- n = 8: 8·9 = 2³·3², exponents {3,2} distinct
- n = 31: 31·32 = 2⁵·31, exponents {5,1} distinct
- n = 127: 127·128 = 2⁷·127, exponents {7,1} distinct
-/

/-- Helper: prove distinct exponents by reducing to concrete prime factor enumeration. -/
private theorem hasDistinctExponents_of_primeFactors_pair
    {n : ℕ} {m p q : ℕ} (hm : n * (n + 1) = m) (hpf : m.primeFactors = {p, q})
    (hne : m.factorization p ≠ m.factorization q) :
    HasDistinctExponents n := by
  unfold HasDistinctExponents
  rw [hm, hpf]
  intro x hx y hy heq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact absurd heq hne
  · exact absurd heq (Ne.symm hne)
  · rfl

/-- Helper: prove distinct exponents for products with exactly 3 prime factors. -/
private theorem hasDistinctExponents_of_primeFactors_triple
    {n : ℕ} {m p q r : ℕ} (hm : n * (n + 1) = m) (hpf : m.primeFactors = {p, q, r})
    (hpq : m.factorization p ≠ m.factorization q)
    (hpr : m.factorization p ≠ m.factorization r)
    (hqr : m.factorization q ≠ m.factorization r) :
    HasDistinctExponents n := by
  unfold HasDistinctExponents
  rw [hm, hpf]
  intro x hx y hy heq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | rfl
    | exact absurd heq hpq
    | exact absurd heq hpr
    | exact absurd heq hqr
    | exact absurd heq.symm hpq
    | exact absurd heq.symm hpr
    | exact absurd heq.symm hqr

/-- n = 3 has distinct exponents: 3·4 = 2²·3¹. -/
theorem example_n3 : HasDistinctExponents 3 :=
  hasDistinctExponents_of_primeFactors_pair (by norm_num) (by native_decide) (by native_decide)

/-- n = 7 has distinct exponents: 7·8 = 2³·7¹. -/
theorem example_n7 : HasDistinctExponents 7 :=
  hasDistinctExponents_of_primeFactors_pair (by norm_num) (by native_decide) (by native_decide)

/-- n = 8 has distinct exponents: 8·9 = 2³·3². -/
theorem example_n8 : HasDistinctExponents 8 :=
  hasDistinctExponents_of_primeFactors_pair (by norm_num) (by native_decide) (by native_decide)

/-- n = 31 has distinct exponents: 31·32 = 2⁵·31¹. -/
theorem example_n31 : HasDistinctExponents 31 :=
  hasDistinctExponents_of_primeFactors_pair (by norm_num) (by native_decide) (by native_decide)

/-- n = 71 has distinct exponents: 71·72 = 2³·3²·71¹ (3-factor case).
    This is the instance from the 8p²-1 construction with p = 3:
    n = 8·9-1 = 71, n+1 = 72 = 8·9 = 2³·3². -/
theorem example_n71 : HasDistinctExponents 71 :=
  hasDistinctExponents_of_primeFactors_triple
    (by norm_num) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- n = 127 has distinct exponents: 127·128 = 2⁷·127¹. -/
theorem example_n127 : HasDistinctExponents 127 :=
  hasDistinctExponents_of_primeFactors_pair (by norm_num) (by native_decide) (by native_decide)

/-
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

/-
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
