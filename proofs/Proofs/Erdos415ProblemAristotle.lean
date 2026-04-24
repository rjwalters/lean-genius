/-
  Aristotle targets for Erdős Problem #415 (Ordering Patterns in Euler's Totient Function)
  Routine supporting lemmas for automated proof search.
  See Erdos415Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main asymptotic results (erdos_1936_F_asymptotic, etc.)
  - NOT definition sorries (NaturalPattern, AlternatingPattern, F_exists, F_sigma_exists)
  - NOT the axiom F_tau declaration
  - Routine properties of the totient function that follow from Mathlib

  Excluded (too deep or malformed for Aristotle):
  - erdos_1936_F_asymptotic: F(n) ≍ log log log n (deep analytic number theory)
  - erdos_1936_F_sigma_asymptotic: deep analytic number theory
  - erdos_1936_F_tau_asymptotic: deep analytic number theory
  - phi_small_values: deep (requires Erdős–Φ estimates)
  - phi_range_size: deep (prime counting function estimates)
  - phi_collisions: statement is bounded but k is unbounded (ill-typed statement)
  - patterns_k2_achievable / patterns_k3_achievable: require specific computation
  - NaturalPattern / AlternatingPattern: definition sorries
  - F_exists / F_sigma_exists: definition sorry in where clauses
  - F_tau: axiom declaration (cannot be proved)
-/
import Mathlib
import Proofs.Erdos415Problem

open Nat Function Finset

namespace Erdos415Aristotle

/-- φ(2p) = p - 1 for odd prime p.
    Strategy: φ(2p) = φ(2) * φ(p) since gcd(2, p) = 1 for odd p.
    φ(2) = 1, φ(p) = p - 1, so φ(2p) = p - 1. -/
theorem phi_2p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : phi (2 * p) = p - 1 := by
  sorry

/-- Consecutive primes give strictly increasing φ values.
    Strategy: φ(p) = p - 1, φ(q) = q - 1, and p < q → p - 1 < q - 1. -/
theorem phi_consecutive_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    phi p < phi q := by
  sorry

end Erdos415Aristotle
