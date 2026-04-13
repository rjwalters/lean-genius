/-
  Aristotle targets for Erdős Problem #456: Smallest Prime ≡ 1 (mod n) vs Smallest m with n | φ(m)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos456Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open problems (parts 1-3 of Erdős #456)
  - NOT theorems depending on axiomatized bounds (Linnik, Erdős strict inequality)
  - Routine properties of Nat.totient and prime divisibility
  - No definition sorries
  - No axioms

  Included targets (5):
  - totient_pos: 0 < Nat.totient n for n ≥ 1
  - totient_le: Nat.totient n ≤ n for all n
  - totient_one_eq_one: Nat.totient 1 = 1
  - dvd_totient_prime: n ∣ p - 1 → n ∣ Nat.totient p (for prime p)
  - prime_ge_two: p.Prime → 2 ≤ p
-/
import Mathlib

open Nat

namespace Erdos456Aristotle

-- Routine: Euler's totient is positive for positive inputs.
-- totient 0 = 0, but totient n > 0 for n ≥ 1.
theorem totient_pos (n : ℕ) (hn : 1 ≤ n) : 0 < n.totient := by
  sorry

-- Routine: Euler's totient satisfies φ(n) ≤ n.
-- A standard bound on the totient function.
theorem totient_le (n : ℕ) : n.totient ≤ n := by
  sorry

-- Routine: φ(1) = 1.
-- Only 1 is coprime to 1.
theorem totient_one_eq_one : Nat.totient 1 = 1 := by
  sorry

-- Routine: for prime p, n ∣ (p - 1) implies n ∣ φ(p).
-- Since φ(p) = p - 1 for primes.
theorem dvd_totient_prime (n p : ℕ) (hp : p.Prime) (h : n ∣ p - 1) :
    n ∣ p.totient := by
  sorry

-- Routine: primes are at least 2.
-- The minimal prime is 2.
theorem prime_ge_two (p : ℕ) (hp : p.Prime) : 2 ≤ p := by
  sorry

end Erdos456Aristotle
