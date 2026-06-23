/-
# Weak Goldbach Conjecture (Ternary Goldbach)

Every odd integer greater than 5 is the sum of three primes.

**Status**: Proved by Helfgott (2013). This file formalizes:
1. The statement
2. Computational verification for small cases
3. Infrastructure for future work

**References**:
- Helfgott, "The ternary Goldbach conjecture is true" (2013)
- Vinogradov, "Representation of an odd number as sum of three primes" (1937)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace WeakGoldbach

/-- A number is a sum of three primes -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- The Weak Goldbach Conjecture -/
def WeakGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n

/-- 7 = 2 + 2 + 3 -/
theorem goldbach_7 : IsSumOfThreePrimes 7 := by
  use 2, 2, 3
  refine ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, ?_⟩
  rfl

/-- 9 = 3 + 3 + 3 -/
theorem goldbach_9 : IsSumOfThreePrimes 9 := by
  use 3, 3, 3
  refine ⟨Nat.prime_three, Nat.prime_three, Nat.prime_three, ?_⟩
  rfl

/-- 11 = 3 + 3 + 5 -/
theorem goldbach_11 : IsSumOfThreePrimes 11 := by
  use 3, 3, 5
  refine ⟨Nat.prime_three, Nat.prime_three, ?_, ?_⟩
  · decide
  · rfl

/-- 13 = 3 + 3 + 7 -/
theorem goldbach_13 : IsSumOfThreePrimes 13 := by
  use 3, 3, 7
  refine ⟨Nat.prime_three, Nat.prime_three, ?_, ?_⟩
  · decide
  · rfl

/-- 15 = 3 + 5 + 7 -/
theorem goldbach_15 : IsSumOfThreePrimes 15 := by
  use 3, 5, 7
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 17 = 5 + 5 + 7 -/
theorem goldbach_17 : IsSumOfThreePrimes 17 := by
  use 5, 5, 7
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 19 = 3 + 5 + 11 -/  
theorem goldbach_19 : IsSumOfThreePrimes 19 := by
  use 3, 5, 11
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 21 = 7 + 7 + 7 -/
theorem goldbach_21 : IsSumOfThreePrimes 21 := by
  use 7, 7, 7
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- Vinogradov (1937): sufficiently large odd numbers are sums of 3 primes -/
axiom vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n

/-- Helfgott (2013): the weak Goldbach conjecture is true -/
axiom helfgott_weak_goldbach : WeakGoldbachConjecture

/-- Every odd n > 5 is sum of three primes -/
theorem weak_goldbach (n : ℕ) (hn : n > 5) (hodd : Odd n) :
    IsSumOfThreePrimes n :=
  helfgott_weak_goldbach n hn hodd

end WeakGoldbach
