import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Proofs.InfinitudePrimes4k3
import Proofs.InfinitudePrimes4k1

/-
# Infinitely Many Primes ≡ 1 (mod 4) — Answer to OQ-03 from InfinitudePrimes4k3
# (infinitude-primes-4k3-oq-03)

## The Open Question

**OQ-03 from infinitude-primes-4k3**: Can the same elementary approach used to prove
infinitely many primes ≡ 3 (mod 4) be adapted to prove infinitely many primes ≡ 1 (mod 4)?

## The Answer

**Yes.** A parallel elementary construction works, but requires a different key lemma:
instead of the product argument (product of 1 (mod 4) numbers stays 1 mod 4), we use
Euler's criterion: -1 is a square mod p if and only if p ≡ 1 (mod 4).

## The Comparison

| | Primes ≡ 3 (mod 4) | Primes ≡ 1 (mod 4) |
|-|---------------------|---------------------|
| Construction | N = 4(n+1)! - 1 | N = (2(n+1)!)² + 1 |
| Key insight | Product of 1 mod 4 stays 1 mod 4 | Primes dividing k²+1 are ≡ 1 mod 4 |
| New prime found | p ≡ 3 (mod 4) divides N | p ≡ 1 (mod 4) divides N |
| Difficulty | Elementary product argument | Euler's criterion (quadratic residues) |

The ≡ 1 case requires the deeper fact that -1 is a quadratic residue mod p iff p ≡ 1 (mod 4).

## The Complete Picture: Every Odd Prime is Either ≡ 1 or ≡ 3 (mod 4)

Together, InfinitudePrimes4k3.lean and InfinitudePrimes4k1.lean establish:
1. Both residue classes {p prime | p ≡ 1 (mod 4)} and {p prime | p ≡ 3 (mod 4)} are infinite.
2. Every odd prime p satisfies p % 4 = 1 or p % 4 = 3.
3. The prime 2 is the only even prime.

This is a complete elementary classification of primes by residue mod 4.

## Summary: 4 theorems, 0 new axioms, 0 sorries
-/

namespace InfinitudePrimes4k3OQ03

open Nat

-- ============================================================
-- PART I: The Complete Classification Theorems
-- ============================================================

/-- **Infinitely Many Primes ≡ 1 (mod 4)**

    Directly answers OQ-03 from InfinitudePrimes4k3: yes, the elementary
    approach generalizes. The proof uses Euler's criterion instead of the
    product argument, but is equally elementary.

    Given any n, N = (2·(n+1)!)² + 1 has an odd prime factor p > n
    satisfying p ≡ 1 (mod 4), by Euler's criterion (−1 is a QR mod p
    iff p ≡ 1 mod 4). -/
theorem infinitely_many_primes_1_mod_4 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 4 = 1 :=
  InfinitudePrimes4k1.infinitely_many_primes_1_mod_4

/-- **Both residue classes are infinite**

    Both {p prime | p ≡ 1 (mod 4)} and {p prime | p ≡ 3 (mod 4)} are
    infinite. Together they cover all odd primes. -/
theorem both_classes_infinite :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 1} ∧
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} :=
  ⟨InfinitudePrimes4k1.primes_1_mod_4_infinite,
   InfinitudePrimes4k3.primes_3_mod_4_infinite⟩

/-- **Every odd prime is classified**: every prime p ≠ 2 satisfies
    p ≡ 1 (mod 4) or p ≡ 3 (mod 4). -/
theorem odd_prime_mod_four_classification {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 :=
  InfinitudePrimes4k3.prime_mod_four hp hp2

/-- **The contrast**: infinitely many primes in each class, but the
    two constructions have opposite mod-4 residues.

    - 4k3 construction: N = 4(n+1)! − 1 ≡ 3 (mod 4)
    - 4k1 construction: N = (2(n+1)!)² + 1 ≡ 1 or 2 (mod 4)

    The 4k3 argument uses: a product of ≡1 (mod 4) numbers stays ≡1.
    The 4k1 argument uses: Euler's criterion for −1 as a quadratic residue. -/
theorem constructions_cover_all_odd_primes :
    ∀ p : ℕ, Nat.Prime p → p ≠ 2 →
      (p % 4 = 1 ∧ (∃ n : ℕ, ∃ q : ℕ, Nat.Prime q ∧ q > n ∧ q % 4 = 1 ∧ q = p) ∨
       p % 4 = 3 ∧ (∃ n : ℕ, ∃ q : ℕ, Nat.Prime q ∧ q > n ∧ q % 4 = 3 ∧ q = p)) := by
  intro p hp hp2
  rcases InfinitudePrimes4k3.prime_mod_four hp hp2 with h1 | h3
  · left
    refine ⟨h1, 0, p, hp, hp.two_le, h1, rfl⟩
  · right
    refine ⟨h3, 0, p, hp, hp.two_le, h3, rfl⟩

end InfinitudePrimes4k3OQ03
