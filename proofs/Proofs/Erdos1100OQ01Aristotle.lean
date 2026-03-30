/-
  Aristotle targets for Erdős Problem #1100 (OQ-01)
  Routine supporting lemmas for automated proof search.
  See Erdos1100ProblemProvable.lean for the main formalization.

  These lemmas support proving tau_perp_equality_infinitely_often:
  "For infinitely many n, τ⊥(n) = ω(n)."
  Strategy: prime numbers are witnesses (τ⊥(p) = 1 = ω(p)).

  Criteria for inclusion:
  - NOT the main open conjecture (τ⊥(n)/ω(n) → ∞ for almost all n)
  - Known results likely in Mathlib
  - Clean theorem statements with no definition sorries
  - No axiom declarations
-/

import Mathlib

open Nat Finset

namespace Erdos1100OQ01

/-
## Supporting lemmas for τ⊥(p) = ω(p) = 1 for primes
-/

/--
ω(p) = 1 for any prime p: a prime has exactly one distinct prime factor.
-/
theorem omega_prime (p : ℕ) (hp : Nat.Prime p) :
    p.primeFactors.card = 1 := by sorry

/--
The divisor count of a prime is 2: divisors of p are {1, p}.
-/
theorem tau_prime (p : ℕ) (hp : Nat.Prime p) :
    (Finset.filter (· ∣ p) (Finset.range (p + 1))).card = 2 := by sorry

/--
The set of divisors of a prime p in {0, ..., p} is exactly {1, p}.
-/
theorem divisors_of_prime (p : ℕ) (hp : Nat.Prime p) :
    Finset.filter (· ∣ p) (Finset.range (p + 1)) = {1, p} := by sorry

/--
gcd(1, n) = 1 for any n: 1 is coprime to everything.
-/
theorem gcd_one_left_eq (n : ℕ) : Nat.gcd 1 n = 1 := by sorry

/--
For a squarefree number n with ω(n) = 1, n is prime.
-/
theorem squarefree_omega_one_is_prime (n : ℕ) (hn : n > 1)
    (hsf : Squarefree n) (hω : n.primeFactors.card = 1) :
    Nat.Prime n := by sorry

/--
Infinitude of primes: for any N, there exists a prime p > N.
(Standard result, should be in Mathlib.)
-/
theorem exists_prime_gt (N : ℕ) : ∃ p : ℕ, p > N ∧ Nat.Prime p := by sorry

end Erdos1100OQ01
