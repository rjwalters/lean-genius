/-
  Aristotle targets for Erdős Problem #415
  Routine supporting lemmas for automated proof search.
  See Erdos415Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open questions (F(n) asymptotics, ordering pattern frequency)
  - NOT theorems depending on def-sorries (F, NaturalPattern, AlternatingPattern)
  - Routine supporting facts: totient function identities, ordering pattern basics
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos415Aristotle

open Nat Finset

/-- Euler's totient function. -/
def phi : ℕ → ℕ := Nat.totient

-- Routine: φ(p) = p - 1 for prime p.
-- Mathlib: Nat.totient_prime.
theorem phi_prime (p : ℕ) (hp : p.Prime) : phi p = p - 1 := by
  exact Nat.totient_prime hp

-- Routine: φ(2p) = p - 1 for an odd prime p.
-- Since p is an odd prime, gcd(2, p) = 1, so φ(2p) = φ(2)·φ(p) = 1·(p-1) = p-1.
theorem phi_2p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : phi (2 * p) = p - 1 := by
  sorry

-- Routine: φ(p) < φ(q) for primes p < q.
-- For primes: φ(p) = p - 1 and φ(q) = q - 1. Since p < q and both ≥ 2, p - 1 < q - 1.
theorem phi_consecutive_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    phi p < phi q := by
  sorry

-- Routine: φ(n) ≥ 1 for all n ≥ 1.
-- The identity element 1 is always coprime to n.
theorem phi_pos (n : ℕ) (hn : n ≥ 1) : phi n ≥ 1 := by
  sorry

-- Routine: φ(n) ≤ n for all n ≥ 1.
-- The count of coprime residues cannot exceed n itself.
theorem phi_le (n : ℕ) (hn : n ≥ 1) : phi n ≤ n := by
  sorry

-- Routine: φ(1) = 1.
-- The only integer coprime to 1 is 1 itself.
theorem phi_one : phi 1 = 1 := by
  sorry

-- Routine: φ(2) = 1.
-- Only 1 is coprime to 2 among {1, 2}.
theorem phi_two : phi 2 = 1 := by
  sorry

-- Routine: For a prime p, p ≥ 2.
-- Every prime is at least 2.
theorem prime_ge_two (p : ℕ) (hp : p.Prime) : p ≥ 2 := hp.two_le

-- Routine: For primes p < q, φ(p) < q - 1.
-- φ(p) = p - 1 < q - 1 since p < q.
theorem phi_prime_lt_pred (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    phi p < q - 1 := by
  sorry

-- Routine: The number of permutations of Fin k is k!.
-- Standard Mathlib: Fintype.card_perm.
theorem orderingPattern_card (k : ℕ) :
    Fintype.card (Equiv.Perm (Fin k)) = k.factorial := by
  simp [Fintype.card_perm]

-- Routine: Finset.univ for Equiv.Perm (Fin k) has k! elements.
theorem perm_univ_card (k : ℕ) :
    (Finset.univ : Finset (Equiv.Perm (Fin k))).card = k.factorial := by
  sorry

-- Routine: k! ≥ 1 for all k.
-- The empty permutation is the identity.
theorem factorial_pos (k : ℕ) : k.factorial ≥ 1 := Nat.factorial_pos k

-- Routine: For all m : ℕ and n : ℕ, m + (n + 1) > n.
-- Pure arithmetic: adding a positive number gives strictly more.
theorem add_succ_gt (m n : ℕ) : m + (n + 1) > n := by
  omega

end Erdos415Aristotle
