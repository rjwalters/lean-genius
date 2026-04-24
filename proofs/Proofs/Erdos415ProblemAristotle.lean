/-
  Aristotle targets for Erdős Problem #415
  Routine supporting lemmas about Euler's totient function for automated proof search.
  See Erdos415Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open questions about ordering patterns in phi(m+1), ..., phi(m+k)
  - NOT the triple-log asymptotics (Erdős 1936 main result)
  - Basic properties of phi = Nat.totient that support the main file
  - No definition sorries, no axioms, no open conjectures

  Included targets (3):
  - phi_2p: totient(2p) = p - 1 for odd prime p
  - phi_consecutive_primes: totient(p) < totient(q) for primes p < q
  - phi_pos: totient(n) ≥ 1 for n ≥ 1

  Excluded (OPEN or deep results):
  - erdos_1936_F_asymptotic: F(n) = Θ(log log log n) (the main Erdős problem)
  - phi_small_values: requires Mertens-type estimates
  - phi_range_size: requires analytic number theory
  - phi_collisions: requires structure of totient values
  - patterns_k2_achievable / patterns_k3_achievable: require pattern search
-/

import Mathlib

namespace Erdos415.Aristotle

open Nat

/- Definitions mirrored from main file -/
def phi : ℕ → ℕ := Nat.totient

/- ## Routine totient properties -/

/-- totient(2p) = p - 1 for odd prime p.
    Proof: gcd(2, p) = 1, so totient(2p) = totient(2) * totient(p) = 1 * (p-1) = p-1. -/
theorem phi_2p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : phi (2 * p) = p - 1 := by
  sorry

/-- For primes p < q, totient(p) < totient(q).
    Proof: totient(p) = p - 1 and totient(q) = q - 1 for primes, and p < q implies p - 1 < q - 1. -/
theorem phi_consecutive_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    phi p < phi q := by
  sorry

/-- totient(n) ≥ 1 for all n ≥ 1.
    Proof: 1 is always coprime to n, so totient(n) ≥ 1. -/
theorem phi_pos (n : ℕ) (hn : n ≥ 1) : phi n ≥ 1 := by
  sorry

end Erdos415.Aristotle
