/-
  Aristotle targets for Erdős Problem #415
  Routine supporting lemmas about arithmetic functions for automated proof search.
  See Stubs/Erdos415Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open questions about ordering patterns in φ(m+1), ..., φ(m+k)
  - Basic properties of Euler's totient φ, divisor sum σ, divisor count τ, prime factors ω
  - No definition sorries
  - No axioms

  Included targets (5):
  - phi_pos: totient is positive for positive inputs
  - phi_prime: totient of a prime p equals p - 1
  - tau_pos: number of divisors is positive for positive inputs
  - sigma_pos: sum of divisors is positive for positive inputs
  - omega_prime: prime has exactly one prime factor

  Excluded (OPEN or deep results):
  - F_triple_log: F(n) = (c + o(1)) log log log n (the actual Erdős problem)
  - decreasing_pattern_first_fail: ordering pattern conjecture (open)
  - natural_ordering_most_likely: pattern frequency conjecture (open)
-/

import Mathlib

namespace Erdos415Aristotle

-- Routine: Euler's totient function is at least 1 for positive n.
-- Standard result: totient(n) ≥ 1 for all n ≥ 1.
theorem phi_pos (n : ℕ) (hn : n ≥ 1) : Nat.totient n ≥ 1 := by
  sorry

-- Routine: For a prime p, totient(p) = p - 1.
-- Standard result: the only number less than p not coprime to p would require a common factor,
-- but p is prime, so all 1, ..., p-1 are coprime to p.
theorem phi_prime (p : ℕ) (hp : p.Prime) : Nat.totient p = p - 1 := by
  sorry

-- Routine: The number of divisors of n is at least 1 for positive n.
-- Since n divides itself, n ∈ Nat.divisors n when n ≥ 1.
theorem tau_pos (n : ℕ) (hn : n ≥ 1) : (Nat.divisors n).card ≥ 1 := by
  sorry

-- Routine: The sum of divisors of n is at least 1 for positive n.
-- Since n ∈ Nat.divisors n and n ≥ 1, the sum is at least 1.
theorem sigma_pos (n : ℕ) (hn : n ≥ 1) : (Nat.divisors n).sum id ≥ 1 := by
  sorry

-- Routine: A prime p has exactly one prime factor, namely p itself.
-- primeFactors p = {p} for prime p, so cardinality is 1.
theorem omega_prime (p : ℕ) (hp : p.Prime) : p.primeFactors.card = 1 := by
  sorry

end Erdos415Aristotle
