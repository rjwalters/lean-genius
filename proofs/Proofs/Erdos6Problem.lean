/-
  Erdős Problem #6: Monotone Sequences of Prime Gaps

  Source: https://erdosproblems.com/6
  Status: SOLVED
  Prize: $100

  Statement:
  Let d_n = p_{n+1} - p_n be the gap between consecutive primes.
  Are there infinitely many n such that d_n < d_{n+1} < d_{n+2}?

  History:
  - Erdős-Turán (1948): Posed this conjecture
  - Erdős was confident it was true, offering substantial money only for disproof
  - Banks-Freiberg-Turnage-Butterbaugh (2015): Proved affirmatively using
    the Maynard-Tao machinery on bounded gaps between primes

  Generalization:
  For any m ≥ 1, there are infinitely many n with:
  - d_n < d_{n+1} < ... < d_{n+m}  (strictly increasing sequences)
  - d_n > d_{n+1} > ... > d_{n+m}  (strictly decreasing sequences)

  This file formalizes the definitions and main results.
-/

import Mathlib

open Nat Set

namespace Erdos6

/-! ## Prime Gap Definition -/

/-- The n-th prime number (0-indexed: p_0 = 2, p_1 = 3, p_2 = 5, ...) -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: d_n = p_{n+1} - p_n -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Alternative notation: d_n for the n-th prime gap -/
notation "d_" n => primeGap n

/-! ## Basic Properties -/

/-- The set of primes is infinite. -/
theorem primes_infinite : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

/-- The n-th prime function is strictly monotone. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono primes_infinite

/-- Prime gaps are positive (p_{n+1} > p_n for all n) -/
theorem primeGap_pos (n : ℕ) : primeGap n > 0 := by
  unfold primeGap nthPrime
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono primes_infinite (Nat.lt_succ_self n)
  omega

/-- The first few prime gaps -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

theorem primeGap_one : primeGap 1 = 2 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-! ## Monotone Sequences -/

/-- A sequence of m consecutive prime gaps starting at n is strictly increasing -/
def HasIncreasingGaps (n m : ℕ) : Prop :=
  ∀ i : ℕ, i < m → primeGap (n + i) < primeGap (n + i + 1)

/-- A sequence of m consecutive prime gaps starting at n is strictly decreasing -/
def HasDecreasingGaps (n m : ℕ) : Prop :=
  ∀ i : ℕ, i < m → primeGap (n + i) > primeGap (n + i + 1)

/-- There are infinitely many starting points with increasing gaps of length m -/
def InfinitelyManyIncreasing (m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n > N, HasIncreasingGaps n m

/-- There are infinitely many starting points with decreasing gaps of length m -/
def InfinitelyManyDecreasing (m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n > N, HasDecreasingGaps n m

/-! ## The Main Conjecture (Original Statement) -/

/--
**Erdős Problem 6: Monotone Prime Gap Triples**

The original question asks: Are there infinitely many n with d_n < d_{n+1} < d_{n+2}?

This is the special case m = 2 of the general increasing gaps problem.
-/
def erdos_6_conjecture : Prop := InfinitelyManyIncreasing 2

/-! ## Main Theorem (Banks-Freiberg-Turnage-Butterbaugh 2015) -/

/--
**Banks-Freiberg-Turnage-Butterbaugh Theorem (2015)**

For any m ≥ 1, there are infinitely many n such that
d_n < d_{n+1} < ... < d_{n+m}.

This was proved using the Maynard-Tao machinery on bounded gaps between primes,
which itself builds on the groundbreaking work of Zhang (2013) proving bounded
gaps between primes.
-/
axiom banks_freiberg_turnage_butterbaugh (m : ℕ) (hm : m ≥ 1) :
    InfinitelyManyIncreasing m

/-- The decreasing version also holds. -/
axiom banks_freiberg_turnage_butterbaugh_decreasing (m : ℕ) (hm : m ≥ 1) :
    InfinitelyManyDecreasing m

/-! ## Resolution of Erdős Problem 6 -/

/-- Erdős Problem 6 is SOLVED: the conjecture is TRUE. -/
theorem erdos_6_solved : erdos_6_conjecture :=
  banks_freiberg_turnage_butterbaugh 2 (by norm_num)

/-- The problem is settled in the affirmative. -/
theorem erdos_6_affirmative : InfinitelyManyIncreasing 2 := erdos_6_solved

/-! ## Maynard-Tao Machinery -/

/--
**Key Ingredient: Bounded Gaps Between Primes**

The proof uses the Maynard-Tao theorem: there exists a constant H such that
infinitely often, there are at least two primes in an interval of length H.

More precisely, for any m, there are infinitely many n such that
among n, n+1, ..., n+H, at least m of these are prime.
-/
axiom maynard_tao_bounded_gaps (m : ℕ) :
    ∃ H : ℕ, ∀ N : ℕ, ∃ n > N, (Finset.filter Nat.Prime (Finset.Icc n (n + H))).card ≥ m

/--
**Zhang's Theorem (2013)**

There exists H such that there are infinitely many pairs of primes
differing by at most H. This was the breakthrough that started the
bounded gaps revolution.
-/
axiom zhang_bounded_gaps : ∃ H : ℕ, ∀ N : ℕ, ∃ p, p > N ∧ Nat.Prime p ∧
    ∃ q, Nat.Prime q ∧ p < q ∧ q - p ≤ H

/-! ## Generalizations -/

/-- There are arbitrarily long increasing runs of prime gaps. -/
theorem arbitrarily_long_increasing_runs :
    ∀ m : ℕ, m ≥ 1 → InfinitelyManyIncreasing m :=
  fun m hm => banks_freiberg_turnage_butterbaugh m hm

/-- There are arbitrarily long decreasing runs of prime gaps. -/
theorem arbitrarily_long_decreasing_runs :
    ∀ m : ℕ, m ≥ 1 → InfinitelyManyDecreasing m :=
  fun m hm => banks_freiberg_turnage_butterbaugh_decreasing m hm

/-! ## Related Concepts -/

/-- The prime gap function is not eventually monotone in either direction.
    That is, both increasing and decreasing patterns occur infinitely often. -/
theorem prime_gaps_oscillate :
    InfinitelyManyIncreasing 1 ∧ InfinitelyManyDecreasing 1 := by
  constructor
  · exact banks_freiberg_turnage_butterbaugh 1 (by norm_num)
  · exact banks_freiberg_turnage_butterbaugh_decreasing 1 (by norm_num)

/-- Average prime gap near n is approximately ln(n) by the Prime Number Theorem. -/
axiom average_prime_gap (n : ℕ) (hn : n ≥ 2) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * Real.log n ≤ (primeGap n : ℝ) + (primeGap (n+1) : ℝ) + (primeGap (n+2) : ℝ) ∧
    (primeGap n : ℝ) + (primeGap (n+1) : ℝ) + (primeGap (n+2) : ℝ) ≤ c₂ * Real.log n

/-! ## Summary

**Problem Status: SOLVED (Affirmative)**

Erdős Problem 6 asks whether there are infinitely many n with d_n < d_{n+1} < d_{n+2}.

**Resolution**:
Banks, Freiberg, and Turnage-Butterbaugh (2015) proved this is TRUE using
the Maynard-Tao machinery on bounded gaps between primes.

**Generalization**:
For any m ≥ 1:
- Infinitely many n with d_n < d_{n+1} < ... < d_{n+m}
- Infinitely many n with d_n > d_{n+1} > ... > d_{n+m}

**Key Techniques**:
- Maynard-Tao sieve methods
- Zhang's bounded gaps breakthrough (2013)
- Careful analysis of prime gaps distribution

References:
- Banks, Freiberg, Turnage-Butterbaugh (2015): "Consecutive primes in tuples"
- Maynard (2015): "Small gaps between primes"
- Zhang (2013): "Bounded gaps between primes"
- Erdős-Turán (1948): Original problem statement
-/

end Erdos6
