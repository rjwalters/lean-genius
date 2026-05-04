/-
  Wilson Primes OQ-01: Are There Infinitely Many Wilson Primes?

  A prime p is a Wilson prime if p² | (p-1)! + 1. The three known Wilson
  primes are 5, 13, and 563. No fourth Wilson prime has been found despite
  exhaustive search below 2 × 10¹³.

  Key results:
  - 5, 13, and 563 are Wilson primes (verified by native_decide)
  - Open conjecture: infinitely many Wilson primes (axiom)
  - Wieferich primes (1093, 3511) proved for analogy

  Status: 1 axiom (infinite conjecture is open)
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace WilsonPrimesOQ01

open Nat

/-! ## Core Definitions -/

/-- A prime p is a **Wilson prime** if p² | (p-1)! + 1.
    Wilson's theorem gives p | (p-1)! + 1 for all primes p;
    Wilson primes are those where the stronger p² condition holds. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ (p - 1).factorial + 1

/-- The **Wilson quotient** W_p = ((p-1)! + 1) / p.
    For every prime p, Wilson's theorem guarantees p | (p-1)! + 1,
    so W_p is a natural number. p is a Wilson prime iff p | W_p. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1).factorial + 1) / p

/-! ## Verified Wilson Primes: 5 and 13 -/

/-- 5 is a Wilson prime: 5² = 25 | 4! + 1 = 25. -/
theorem five_is_wilson_prime : IsWilsonPrime 5 := by
  constructor
  · decide
  · native_decide

/-- 13 is a Wilson prime: 13² = 169 | 12! + 1. -/
theorem thirteen_is_wilson_prime : IsWilsonPrime 13 := by
  constructor
  · decide
  · native_decide

/-! ## The Third Wilson Prime -/

/-- **563 is a Wilson prime**: 563² | 562! + 1.

    Verified by Goldberg (1953) via electronic computer — the first machine
    computation of Wilson primality beyond 13. Subsequently re-verified by
    Crandall, Dilcher, and Pomerance (1997) as part of their extended search
    to 5 × 10⁸.

    Lean 4 native_decide evaluates 562! mod 563² = 316969 via native code. -/
theorem fiveHundredSixtyThree_is_wilson_prime : IsWilsonPrime 563 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-! ## The Open Conjecture -/

/-- **Open Conjecture**: There are infinitely many Wilson primes.

    Density heuristic: the Wilson quotient W_p behaves pseudorandomly modulo p,
    so the probability that p | W_p is heuristically 1/p. Since Σ_{p prime} 1/p
    diverges (Euler 1737), the expected count of Wilson primes up to N is
    approximately log log N → ∞. This mirrors the Wieferich prime heuristic.

    Only three Wilson primes are known: 5, 13, 563. Exhaustive searches have
    reached 2 × 10¹³ (Carlisle, Crandall et al.) without finding a fourth. -/
axiom infinitely_many_wilson_primes :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ IsWilsonPrime p

/-! ## Consequences -/

/-- The three known Wilson primes. -/
theorem three_known_wilson_primes :
    IsWilsonPrime 5 ∧ IsWilsonPrime 13 ∧ IsWilsonPrime 563 :=
  ⟨five_is_wilson_prime, thirteen_is_wilson_prime, fiveHundredSixtyThree_is_wilson_prime⟩

/-- 563 is prime. -/
theorem five_sixty_three_is_prime : Nat.Prime 563 :=
  fiveHundredSixtyThree_is_wilson_prime.1

/-- Under the conjecture, the Wilson prime sequence is unbounded. -/
theorem wilson_primes_unbounded :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ p ^ 2 ∣ (p - 1).factorial + 1 := by
  intro N
  obtain ⟨p, hpN, hpprime, hpwilson⟩ := infinitely_many_wilson_primes N
  exact ⟨p, hpN, hpprime, hpwilson.2⟩

/-- Under the conjecture, there exist Wilson primes arbitrarily large. -/
theorem exists_large_wilson_prime (N : ℕ) : ∃ p : ℕ, p > N ∧ IsWilsonPrime p := by
  obtain ⟨p, hpN, _, hpwilson⟩ := infinitely_many_wilson_primes N
  exact ⟨p, hpN, hpwilson⟩

/-! ## Analogy: Wieferich Primes -/

/-- A **Wieferich prime** is a prime p satisfying p² | 2^(p-1) - 1.
    The pseudorandomness heuristic (probability ~1/p per prime) predicts
    infinitely many Wieferich primes too; none has been proved.
    The only known Wieferich primes are 1093 and 3511 (as of 2026). -/
def IsWieferichPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

/-- 1093 is a Wieferich prime: 1093² | 2^1092 - 1.
    Discovered by Meissner (1913). -/
theorem wieferich_1093 : IsWieferichPrime 1093 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- 3511 is a Wieferich prime: 3511² | 2^3510 - 1.
    Discovered by Beeger (1922). -/
theorem wieferich_3511 : IsWieferichPrime 3511 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

end WilsonPrimesOQ01
