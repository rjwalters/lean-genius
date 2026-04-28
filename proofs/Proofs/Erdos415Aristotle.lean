/-
  Aristotle companion for Erdős Problem #415: Ordering Patterns in Euler's Totient Function

  This file exposes routine lemmas for automated proof search by Aristotle.
  The main formalization is in Erdos415Problem.lean.

  Targets: basic properties of Euler's totient function that follow directly
  from Mathlib's Nat.totient API without depending on the sorry-defined
  F, NaturalPattern, or AlternatingPattern functions.
-/

import Mathlib

namespace Erdos415Aristotle

open Nat

/-- φ(2p) = p - 1 for odd prime p.
    Follows from totient multiplicativity and φ(2) = 1, φ(p) = p - 1. -/
theorem phi_2p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Nat.totient (2 * p) = p - 1 := by
  sorry

/-- Consecutive primes give strictly increasing totient values.
    φ(p) = p - 1 < q - 1 = φ(q) for primes p < q. -/
theorem phi_consecutive_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    Nat.totient p < Nat.totient q := by
  sorry

/-- φ(p) + 1 = p for any prime p. -/
theorem phi_prime_succ (p : ℕ) (hp : p.Prime) :
    Nat.totient p + 1 = p := by
  sorry

end Erdos415Aristotle
