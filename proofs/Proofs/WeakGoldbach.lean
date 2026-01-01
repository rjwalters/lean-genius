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

/-- 23 = 5 + 7 + 11 -/
theorem goldbach_23 : IsSumOfThreePrimes 23 := by
  use 5, 7, 11
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 25 = 5 + 7 + 13 -/
theorem goldbach_25 : IsSumOfThreePrimes 25 := by
  use 5, 7, 13
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 27 = 5 + 11 + 11 -/
theorem goldbach_27 : IsSumOfThreePrimes 27 := by
  use 5, 11, 11
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 29 = 5 + 7 + 17 -/
theorem goldbach_29 : IsSumOfThreePrimes 29 := by
  use 5, 7, 17
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 31 = 7 + 7 + 17 -/
theorem goldbach_31 : IsSumOfThreePrimes 31 := by
  use 7, 7, 17
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 33 = 3 + 7 + 23 -/
theorem goldbach_33 : IsSumOfThreePrimes 33 := by
  use 3, 7, 23
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 35 = 5 + 7 + 23 -/
theorem goldbach_35 : IsSumOfThreePrimes 35 := by
  use 5, 7, 23
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 37 = 7 + 13 + 17 -/
theorem goldbach_37 : IsSumOfThreePrimes 37 := by
  use 7, 13, 17
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 39 = 7 + 13 + 19 -/
theorem goldbach_39 : IsSumOfThreePrimes 39 := by
  use 7, 13, 19
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 41 = 11 + 13 + 17 -/
theorem goldbach_41 : IsSumOfThreePrimes 41 := by
  use 11, 13, 17
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 43 = 7 + 17 + 19 -/
theorem goldbach_43 : IsSumOfThreePrimes 43 := by
  use 7, 17, 19
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 45 = 5 + 17 + 23 -/
theorem goldbach_45 : IsSumOfThreePrimes 45 := by
  use 5, 17, 23
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 47 = 5 + 11 + 31 -/
theorem goldbach_47 : IsSumOfThreePrimes 47 := by
  use 5, 11, 31
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 49 = 3 + 17 + 29 -/
theorem goldbach_49 : IsSumOfThreePrimes 49 := by
  use 3, 17, 29
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 51 = 7 + 7 + 37 -/
theorem goldbach_51 : IsSumOfThreePrimes 51 := by
  use 7, 7, 37
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-! ## Extended Verification (53-101)

Continuing the verification for the next 25 odd numbers.
-/

/-- 53 = 5 + 7 + 41 -/
theorem goldbach_53 : IsSumOfThreePrimes 53 := by
  use 5, 7, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 55 = 3 + 11 + 41 -/
theorem goldbach_55 : IsSumOfThreePrimes 55 := by
  use 3, 11, 41
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 57 = 5 + 11 + 41 -/
theorem goldbach_57 : IsSumOfThreePrimes 57 := by
  use 5, 11, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 59 = 7 + 11 + 41 -/
theorem goldbach_59 : IsSumOfThreePrimes 59 := by
  use 7, 11, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 61 = 3 + 17 + 41 -/
theorem goldbach_61 : IsSumOfThreePrimes 61 := by
  use 3, 17, 41
  refine ⟨Nat.prime_three, ?_, ?_, rfl⟩ <;> decide

/-- 63 = 5 + 17 + 41 -/
theorem goldbach_63 : IsSumOfThreePrimes 63 := by
  use 5, 17, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 65 = 7 + 17 + 41 -/
theorem goldbach_65 : IsSumOfThreePrimes 65 := by
  use 7, 17, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 67 = 7 + 19 + 41 -/
theorem goldbach_67 : IsSumOfThreePrimes 67 := by
  use 7, 19, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 69 = 11 + 17 + 41 -/
theorem goldbach_69 : IsSumOfThreePrimes 69 := by
  use 11, 17, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 71 = 11 + 19 + 41 -/
theorem goldbach_71 : IsSumOfThreePrimes 71 := by
  use 11, 19, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 73 = 13 + 19 + 41 -/
theorem goldbach_73 : IsSumOfThreePrimes 73 := by
  use 13, 19, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 75 = 13 + 19 + 43 -/
theorem goldbach_75 : IsSumOfThreePrimes 75 := by
  use 13, 19, 43
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 77 = 7 + 29 + 41 -/
theorem goldbach_77 : IsSumOfThreePrimes 77 := by
  use 7, 29, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 79 = 11 + 31 + 37 -/
theorem goldbach_79 : IsSumOfThreePrimes 79 := by
  use 11, 31, 37
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 81 = 11 + 29 + 41 -/
theorem goldbach_81 : IsSumOfThreePrimes 81 := by
  use 11, 29, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 83 = 13 + 29 + 41 -/
theorem goldbach_83 : IsSumOfThreePrimes 83 := by
  use 13, 29, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 85 = 11 + 31 + 43 -/
theorem goldbach_85 : IsSumOfThreePrimes 85 := by
  use 11, 31, 43
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 87 = 13 + 31 + 43 -/
theorem goldbach_87 : IsSumOfThreePrimes 87 := by
  use 13, 31, 43
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 89 = 17 + 31 + 41 -/
theorem goldbach_89 : IsSumOfThreePrimes 89 := by
  use 17, 31, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 91 = 19 + 31 + 41 -/
theorem goldbach_91 : IsSumOfThreePrimes 91 := by
  use 19, 31, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 93 = 11 + 41 + 41 -/
theorem goldbach_93 : IsSumOfThreePrimes 93 := by
  use 11, 41, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 95 = 13 + 41 + 41 -/
theorem goldbach_95 : IsSumOfThreePrimes 95 := by
  use 13, 41, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 97 = 7 + 43 + 47 -/
theorem goldbach_97 : IsSumOfThreePrimes 97 := by
  use 7, 43, 47
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 99 = 17 + 41 + 41 -/
theorem goldbach_99 : IsSumOfThreePrimes 99 := by
  use 17, 41, 41
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-- 101 = 5 + 43 + 53 -/
theorem goldbach_101 : IsSumOfThreePrimes 101 := by
  use 5, 43, 53
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide

/-! ## Decidable Instance for IsSumOfThreePrimes

We provide a computable decision procedure for checking if a number
is expressible as a sum of three primes.
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

/-! ## Demonstration of Decidable Instance

The decidable instance allows `decide` to work on IsSumOfThreePrimes for concrete values.
-/

-- These can be proven by decide now (though slower than explicit witnesses)
example : IsSumOfThreePrimes 7 := by decide
example : IsSumOfThreePrimes 9 := by decide
example : IsSumOfThreePrimes 11 := by decide

-- Negative examples: small numbers that are NOT sums of three primes
example : ¬IsSumOfThreePrimes 0 := by decide
example : ¬IsSumOfThreePrimes 1 := by decide
example : ¬IsSumOfThreePrimes 2 := by decide
example : ¬IsSumOfThreePrimes 3 := by decide
example : ¬IsSumOfThreePrimes 4 := by decide
example : ¬IsSumOfThreePrimes 5 := by decide

/-! ## Structural Lemma: Connection to Binary Goldbach

This lemma shows that the weak Goldbach conjecture reduces to
binary Goldbach after subtracting 3.
-/

/-- A number is a sum of two primes (binary Goldbach) -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- Binary Goldbach Conjecture: every even n > 2 is a sum of two primes -/
def BinaryGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 2 → Even n → IsSumOfTwoPrimes n

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

/-! ## Decidable Instance for IsSumOfTwoPrimes

We provide a computable decision procedure for binary Goldbach verification.
-/

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

/-! ## Binary Goldbach Verified Cases

The binary (strong) Goldbach conjecture states every even n > 2 is a sum of two primes.
We verify this for all even numbers from 4 to 50.
-/

-- Verified by decide using the Decidable instance
example : IsSumOfTwoPrimes 4 := by decide   -- 4 = 2 + 2
example : IsSumOfTwoPrimes 6 := by decide   -- 6 = 3 + 3
example : IsSumOfTwoPrimes 8 := by decide   -- 8 = 3 + 5
example : IsSumOfTwoPrimes 10 := by decide  -- 10 = 3 + 7 or 5 + 5
example : IsSumOfTwoPrimes 12 := by decide  -- 12 = 5 + 7
example : IsSumOfTwoPrimes 14 := by decide  -- 14 = 3 + 11 or 7 + 7
example : IsSumOfTwoPrimes 16 := by decide  -- 16 = 3 + 13 or 5 + 11
example : IsSumOfTwoPrimes 18 := by decide  -- 18 = 5 + 13 or 7 + 11
example : IsSumOfTwoPrimes 20 := by decide  -- 20 = 3 + 17 or 7 + 13
example : IsSumOfTwoPrimes 22 := by decide  -- 22 = 3 + 19 or 5 + 17 or 11 + 11
example : IsSumOfTwoPrimes 24 := by decide  -- 24 = 5 + 19 or 7 + 17 or 11 + 13
example : IsSumOfTwoPrimes 26 := by decide  -- 26 = 3 + 23 or 7 + 19 or 13 + 13
example : IsSumOfTwoPrimes 28 := by decide  -- 28 = 5 + 23 or 11 + 17
example : IsSumOfTwoPrimes 30 := by decide  -- 30 = 7 + 23 or 11 + 19 or 13 + 17
example : IsSumOfTwoPrimes 32 := by decide  -- 32 = 3 + 29 or 13 + 19
example : IsSumOfTwoPrimes 34 := by decide  -- 34 = 3 + 31 or 5 + 29 or 11 + 23 or 17 + 17
example : IsSumOfTwoPrimes 36 := by decide  -- 36 = 5 + 31 or 7 + 29 or 13 + 23 or 17 + 19
example : IsSumOfTwoPrimes 38 := by decide  -- 38 = 7 + 31 or 19 + 19
example : IsSumOfTwoPrimes 40 := by decide  -- 40 = 3 + 37 or 11 + 29 or 17 + 23
example : IsSumOfTwoPrimes 42 := by decide  -- 42 = 5 + 37 or 11 + 31 or 13 + 29 or 19 + 23
example : IsSumOfTwoPrimes 44 := by decide  -- 44 = 3 + 41 or 7 + 37 or 13 + 31
example : IsSumOfTwoPrimes 46 := by decide  -- 46 = 3 + 43 or 5 + 41 or 17 + 29 or 23 + 23
example : IsSumOfTwoPrimes 48 := by decide  -- 48 = 5 + 43 or 7 + 41 or 11 + 37 or 17 + 31 or 19 + 29
example : IsSumOfTwoPrimes 50 := by decide  -- 50 = 3 + 47 or 7 + 43 or 13 + 37 or 19 + 31

-- Negative examples: small numbers or odd numbers
example : ¬IsSumOfTwoPrimes 0 := by decide
example : ¬IsSumOfTwoPrimes 1 := by decide
example : ¬IsSumOfTwoPrimes 2 := by decide
example : ¬IsSumOfTwoPrimes 3 := by decide

/-! ## Summary of Verified Cases

The weak Goldbach conjecture has been computationally verified for all odd n with 7 ≤ n ≤ 101:
- 7 to 51: 23 cases (original)
- 53 to 101: 25 cases (extended)
- Total: 48 consecutive odd numbers

This covers 48 consecutive odd numbers. Each verification provides an explicit witness (p, q, r)
such that n = p + q + r with all three being prime.
-/

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
