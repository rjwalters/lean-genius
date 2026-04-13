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
    p.primeFactors.card = 1 := by
  rw [Nat.Prime.primeFactors hp]
  simp

/--
The set of divisors of a prime p in {0, ..., p} is exactly {1, p}.
-/
theorem divisors_of_prime (p : ℕ) (hp : Nat.Prime p) :
    Finset.filter (· ∣ p) (Finset.range (p + 1)) = {1, p} := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun ⟨_, hd⟩ => hp.eq_one_or_self_of_dvd d hd, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨by linarith [hp.one_lt], one_dvd _⟩
  · exact ⟨Nat.lt_succ_iff.mpr le_rfl, dvd_refl _⟩

/--
The divisor count of a prime is 2: divisors of p are {1, p}.
-/
theorem tau_prime (p : ℕ) (hp : Nat.Prime p) :
    (Finset.filter (· ∣ p) (Finset.range (p + 1))).card = 2 := by
  rw [divisors_of_prime p hp]
  rw [Finset.card_pair (by exact hp.one_lt.ne'.symm)]

/--
gcd(1, n) = 1 for any n: 1 is coprime to everything.
-/
theorem gcd_one_left_eq (n : ℕ) : Nat.gcd 1 n = 1 := Nat.gcd_one_left n

/-
PROBLEM
For a squarefree number n with ω(n) = 1, n is prime.

PROVIDED SOLUTION
From hω, use Finset.card_eq_one to get that n.primeFactors = {p} for some prime p. Then since n is squarefree, n equals the product of its prime factors (Nat.Squarefree.eq_prod_primeFactors or similar). The product of {p} is just p, so n = p, hence n is prime.
-/
theorem squarefree_omega_one_is_prime (n : ℕ) (hn : n > 1)
    (hsf : Squarefree n) (hω : n.primeFactors.card = 1) :
    Nat.Prime n := by
      -- Let p be the single prime factor of n.
      obtain ⟨p, hp⟩ : ∃ p, n.primeFactors = {p} := by
        exact Finset.card_eq_one.mp hω;
      -- Since n is squarefree and has exactly one distinct prime factor p, n must be equal to p.
      have hn_eq_p : n = p := by
        rw [ ← Nat.prod_primeFactors_of_squarefree hsf, hp, Finset.prod_singleton ];
      exact hn_eq_p ▸ Nat.prime_of_mem_primeFactors ( hp.symm ▸ Finset.mem_singleton_self _ )

/--
Infinitude of primes: for any N, there exists a prime p > N.
(Standard result, should be in Mathlib.)
-/
theorem exists_prime_gt (N : ℕ) : ∃ p : ℕ, p > N ∧ Nat.Prime p := by
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p, by omega, hp_prime⟩

end Erdos1100OQ01