/-
# Weak Goldbach Conjecture (Ternary Goldbach)

Every odd integer greater than 5 is the sum of three primes.

**Status**: Proved by Helfgott (2013). This file formalizes:
1. The formal statement
2. Decidable instances for computational verification
3. Structural reduction: Binary Goldbach ⟹ Weak Goldbach

**References**:
- Helfgott, "The ternary Goldbach conjecture is true" (2013)
- Vinogradov, "Representation of an odd number as sum of three primes" (1937)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace WeakGoldbach

/-! ## Core Definitions -/

/-- A number is a sum of three primes -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- The Weak Goldbach Conjecture -/
def WeakGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n

/-- A number is a sum of two primes (binary Goldbach) -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- Binary Goldbach Conjecture: every even n > 2 is a sum of two primes -/
def BinaryGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 2 → Even n → IsSumOfTwoPrimes n

/-! ## Example Verifications

A few examples demonstrating the explicit witness approach.
The decidable instances below allow automated verification of any specific case.
-/

/-- 7 = 2 + 2 + 3 -/
theorem goldbach_7 : IsSumOfThreePrimes 7 := by
  use 2, 2, 3
  refine ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- 9 = 3 + 3 + 3 -/
theorem goldbach_9 : IsSumOfThreePrimes 9 := by
  use 3, 3, 3
  refine ⟨Nat.prime_three, Nat.prime_three, Nat.prime_three, rfl⟩

/-- 11 = 3 + 3 + 5 -/
theorem goldbach_11 : IsSumOfThreePrimes 11 := by
  use 3, 3, 5
  refine ⟨Nat.prime_three, Nat.prime_three, ?_, rfl⟩
  decide

/-- 21 = 7 + 7 + 7 (example with three identical odd primes) -/
theorem goldbach_21 : IsSumOfThreePrimes 21 := by
  use 7, 7, 7
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 101 = 5 + 43 + 53 (larger example) -/
theorem goldbach_101 : IsSumOfThreePrimes 101 := by
  use 5, 43, 53
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-! ## Decidable Instance for IsSumOfThreePrimes

This infrastructure enables `decide` to automatically verify any specific case.
-/

/-- Check if n = p + q + r for specific primes p, q, r -/
def checkThreePrimes (n p q r : ℕ) : Bool :=
  n = p + q + r && Nat.Prime p && Nat.Prime q && Nat.Prime r

/-- Check if n is a sum of three primes by brute force search -/
def isSumOfThreePrimesDecide (n : ℕ) : Bool :=
  let bound := n
  (List.range (bound + 1)).any fun p =>
    (List.range (bound + 1)).any fun q =>
      (List.range (bound + 1)).any fun r =>
        checkThreePrimes n p q r

/-- The decision procedure is sound: if it returns true, the property holds -/
theorem isSumOfThreePrimesDecide_sound {n : ℕ} (h : isSumOfThreePrimesDecide n = true) :
    IsSumOfThreePrimes n := by
  unfold isSumOfThreePrimesDecide at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨p, ⟨_, hq_ex⟩⟩ := h
  obtain ⟨q, ⟨_, hr_ex⟩⟩ := hq_ex
  obtain ⟨r, ⟨_, hcheck⟩⟩ := hr_ex
  unfold checkThreePrimes at hcheck
  simp only [Bool.and_eq_true] at hcheck
  simp only [decide_eq_true_eq] at hcheck
  exact ⟨p, q, r, hcheck.1.1.2, hcheck.1.2, hcheck.2, hcheck.1.1.1⟩

/-- The decision procedure is complete: if the property holds, it returns true -/
theorem isSumOfThreePrimesDecide_complete {n : ℕ} (h : IsSumOfThreePrimes n) :
    isSumOfThreePrimesDecide n = true := by
  obtain ⟨p, q, r, hp, hq, hr, heq⟩ := h
  unfold isSumOfThreePrimesDecide
  simp only [List.any_eq_true, List.mem_range]
  use p
  constructor
  · omega
  use q
  constructor
  · omega
  use r
  constructor
  · omega
  unfold checkThreePrimes
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨heq, hp⟩, hq⟩, hr⟩

/-- Decidable instance for IsSumOfThreePrimes -/
instance decidableIsSumOfThreePrimes (n : ℕ) : Decidable (IsSumOfThreePrimes n) :=
  if h : isSumOfThreePrimesDecide n then
    isTrue (isSumOfThreePrimesDecide_sound h)
  else
    isFalse (fun hsum => h (isSumOfThreePrimesDecide_complete hsum))

/-! ## Decidable Instance for IsSumOfTwoPrimes -/

/-- Check if n = p + q for specific primes p, q -/
def checkTwoPrimes (n p q : ℕ) : Bool :=
  n = p + q && Nat.Prime p && Nat.Prime q

/-- Check if n is a sum of two primes by brute force search -/
def isSumOfTwoPrimesDecide (n : ℕ) : Bool :=
  let bound := n
  (List.range (bound + 1)).any fun p =>
    (List.range (bound + 1)).any fun q =>
      checkTwoPrimes n p q

/-- The decision procedure is sound: if it returns true, the property holds -/
theorem isSumOfTwoPrimesDecide_sound {n : ℕ} (h : isSumOfTwoPrimesDecide n = true) :
    IsSumOfTwoPrimes n := by
  unfold isSumOfTwoPrimesDecide at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨p, ⟨_, hq_ex⟩⟩ := h
  obtain ⟨q, ⟨_, hcheck⟩⟩ := hq_ex
  unfold checkTwoPrimes at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨p, q, hcheck.1.2, hcheck.2, hcheck.1.1⟩

/-- The decision procedure is complete: if the property holds, it returns true -/
theorem isSumOfTwoPrimesDecide_complete {n : ℕ} (h : IsSumOfTwoPrimes n) :
    isSumOfTwoPrimesDecide n = true := by
  obtain ⟨p, q, hp, hq, heq⟩ := h
  unfold isSumOfTwoPrimesDecide
  simp only [List.any_eq_true, List.mem_range]
  use p
  constructor
  · omega
  use q
  constructor
  · omega
  unfold checkTwoPrimes
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨heq, hp⟩, hq⟩

/-- Decidable instance for IsSumOfTwoPrimes -/
instance decidableIsSumOfTwoPrimes (n : ℕ) : Decidable (IsSumOfTwoPrimes n) :=
  if h : isSumOfTwoPrimesDecide n then
    isTrue (isSumOfTwoPrimesDecide_sound h)
  else
    isFalse (fun hsum => h (isSumOfTwoPrimesDecide_complete hsum))

/-! ## Demonstration of Decidable Instances

With the decidable instances, `decide` can verify any concrete case automatically.
-/

-- Ternary Goldbach examples via decide
example : IsSumOfThreePrimes 7 := by decide
example : IsSumOfThreePrimes 13 := by decide
example : IsSumOfThreePrimes 15 := by decide

-- Negative examples: small numbers that are NOT sums of three primes
example : ¬IsSumOfThreePrimes 0 := by decide
example : ¬IsSumOfThreePrimes 1 := by decide
example : ¬IsSumOfThreePrimes 5 := by decide

-- Binary Goldbach examples via decide
example : IsSumOfTwoPrimes 4 := by decide   -- 4 = 2 + 2
example : IsSumOfTwoPrimes 10 := by decide  -- 10 = 5 + 5
example : IsSumOfTwoPrimes 20 := by decide  -- 20 = 7 + 13

-- Negative examples for binary
example : ¬IsSumOfTwoPrimes 0 := by decide
example : ¬IsSumOfTwoPrimes 1 := by decide
example : ¬IsSumOfTwoPrimes 2 := by decide

/-! ## Structural Theorem: Binary Goldbach ⟹ Weak Goldbach

This is the key theoretical result: the weak (ternary) Goldbach conjecture
reduces to the binary Goldbach conjecture.
-/

/-- If n = 3 + m where m is a sum of two primes, then n is a sum of three primes -/
theorem sumOfTwoPrimes_add_three {m : ℕ} (hm : IsSumOfTwoPrimes m) :
    IsSumOfThreePrimes (3 + m) := by
  obtain ⟨p, q, hp, hq, heq⟩ := hm
  refine ⟨3, p, q, Nat.prime_three, hp, hq, ?_⟩
  omega

/-- Every odd n > 5 can be written as 3 + even_m for some even m > 2 -/
theorem odd_gt_five_eq_three_plus_even {n : ℕ} (hn : n > 5) (hodd : Odd n) :
    ∃ m : ℕ, m > 2 ∧ Even m ∧ n = 3 + m := by
  use n - 3
  refine ⟨?_, ?_, ?_⟩
  · omega
  · obtain ⟨k, hk⟩ := hodd
    rw [hk]
    use k - 1
    omega
  · omega

/-- Weak Goldbach follows from Binary Goldbach
    (This reduces weak Goldbach to the binary conjecture) -/
theorem binary_implies_weak (h : BinaryGoldbachConjecture) : WeakGoldbachConjecture := by
  intro n hn hodd
  obtain ⟨m, hm_gt, hm_even, hm_eq⟩ := odd_gt_five_eq_three_plus_even hn hodd
  rw [hm_eq]
  apply sumOfTwoPrimes_add_three
  exact h m hm_gt hm_even

/-! ## Axiomatized Results -/

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
