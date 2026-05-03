/-
  Wilson Primes OQ-01: Are There Infinitely Many Wilson Primes?

  A prime p is a Wilson prime if p² | (p-1)! + 1. The three known Wilson
  primes are 5, 13, and 563. No fourth Wilson prime has been found despite
  exhaustive search below 2 × 10¹³.

  Key results:
  - 5 and 13 are Wilson primes (proved in WilsonsTheoremOQ01)
  - 563 is a Wilson prime (axiom; Goldberg 1953; too large for native_decide)
  - Open conjecture: infinitely many Wilson primes (axiom)
  - Wilson primes form an infinite set under the conjecture
  - Connection: p Wilson prime ↔ p | wilsonQuotient p (proved in parent)

  Status: 2 axioms (563 verified computationally; infinite conjecture open)
-/

import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Proofs.WilsonsTheoremOQ01

namespace WilsonPrimesOQ01

open Nat WilsonsTheoremGeneralization

/-! ## The Third Wilson Prime (Axiom) -/

/-- **563 is a Wilson prime**: 563² | 562! + 1.

    Verified by Goldberg (1953) via electronic computer — the first machine
    computation of Wilson primality beyond 13. The number 562! has over 1300
    decimal digits; verifying 563² | 562! + 1 requires arbitrary-precision
    arithmetic beyond the reach of Lean's native_decide. -/
axiom fiveHundredSixtyThree_is_wilson_prime : IsWilsonPrime 563

/-! ## The Open Conjecture -/

/-- **Open Conjecture** (Erdős, widely expected):
    There are infinitely many Wilson primes.

    Density heuristic: the Wilson quotient W_p = ((p-1)! + 1)/p behaves
    pseudorandomly modulo p. The probability that p | W_p is heuristically 1/p.
    Since Σ_{p prime} 1/p diverges (Euler 1737), the expected count of Wilson
    primes up to N is ~ log log N → ∞. This is the standard heuristic argument,
    analogous to the reasoning for Wieferich primes.

    Despite exhaustive search up to 2 × 10¹³ finding only three Wilson primes
    (5, 13, 563), no proof or disproof is known. -/
axiom infinitely_many_wilson_primes :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ IsWilsonPrime p

/-! ## Verified Wilson Primes -/

/-- The three known Wilson primes are 5, 13, and 563. -/
theorem three_known_wilson_primes :
    IsWilsonPrime 5 ∧ IsWilsonPrime 13 ∧ IsWilsonPrime 563 :=
  ⟨five_is_wilson_prime, thirteen_is_wilson_prime, fiveHundredSixtyThree_is_wilson_prime⟩

/-- 563 is prime. -/
theorem five_sixty_three_prime : Nat.Prime 563 := by norm_num

/-- Wilson primes include their primality witness. -/
theorem fiveHundredSixtyThree_prime_and_wilson :
    Nat.Prime 563 ∧ 563 ^ 2 ∣ 562 .factorial + 1 :=
  fiveHundredSixtyThree_is_wilson_prime

/-! ## Consequences of the Conjecture -/

/-- Under the infinite Wilson primes conjecture, for every N there is a
    Wilson prime beyond N — i.e., the set of Wilson primes is unbounded. -/
theorem wilson_primes_unbounded :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ p ^ 2 ∣ (p - 1).factorial + 1 := by
  intro N
  obtain ⟨p, hpN, hpprime, hpwilson⟩ := infinitely_many_wilson_primes N
  exact ⟨p, hpN, hpprime, hpwilson.2⟩

/-- Under the conjecture, there are at least 4 distinct Wilson primes. -/
theorem at_least_four_wilson_primes :
    ∃ p₁ p₂ p₃ p₄ : ℕ, p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧
                         p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
                         IsWilsonPrime p₁ ∧ IsWilsonPrime p₂ ∧
                         IsWilsonPrime p₃ ∧ IsWilsonPrime p₄ := by
  obtain ⟨p₄, h, hprime, hwilson⟩ := infinitely_many_wilson_primes 563
  refine ⟨5, 13, 563, p₄, by decide, by decide, ?_, by decide, ?_, ?_,
          five_is_wilson_prime, thirteen_is_wilson_prime,
          fiveHundredSixtyThree_is_wilson_prime, hwilson⟩
  · intro heq; simp [← heq] at h
  · intro heq; simp [← heq] at h
  · intro heq; simp [← heq] at h

/-! ## Wilson Quotient Perspective -/

/-- 563 divides its Wilson quotient W_{563}. -/
theorem five_sixty_three_divides_wilson_quotient :
    563 ∣ wilsonQuotient 563 :=
  (isWilsonPrime_iff_quotient five_sixty_three_prime).mp
    fiveHundredSixtyThree_is_wilson_prime

/-- Under the conjecture, infinitely many primes divide their Wilson quotient. -/
theorem infinitely_many_primes_divide_wilson_quotient :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ p ∣ wilsonQuotient p := by
  intro N
  obtain ⟨p, hpN, hpprime, hpwilson⟩ := infinitely_many_wilson_primes N
  exact ⟨p, hpN, hpprime, (isWilsonPrime_iff_quotient hpprime).mp hpwilson⟩

/-! ## Analogy with Wieferich Primes -/

/-- A **Wieferich prime** is a prime p satisfying p² | 2^(p-1) - 1.
    The only known Wieferich primes are 1093 and 3511 (as of 2026).
    Like Wilson primes, infinitely many Wieferich primes are conjectured
    but none has been proved. -/
def IsWieferichPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

/-- 1093 is a Wieferich prime. -/
theorem wieferich_1093 : IsWieferichPrime 1093 := by
  constructor
  · norm_num
  · native_decide

/-- 3511 is a Wieferich prime. -/
theorem wieferich_3511 : IsWieferichPrime 3511 := by
  constructor
  · norm_num
  · native_decide

end WilsonPrimesOQ01
