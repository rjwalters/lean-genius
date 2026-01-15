/-
  Erdős Problem #137: Powerful Products of Consecutive Integers

  Let k ≥ 3. Can the product of any k consecutive integers ever be powerful?
  That is, must there always exist a prime p | N such that p² ∤ N?

  **Status**: The main question about powerful numbers remains OPEN.
  **Related result**: Erdős-Selfridge (1975) proved that the product of
  k ≥ 2 consecutive integers can never be a PERFECT POWER.

  A number n is **powerful** if for every prime p dividing n, p² also divides n.
  Equivalently, n = a²b³ for some positive integers a, b.

  Key facts:
  - n(n+1) CAN be powerful for infinitely many n (see Problem #364)
  - But for k ≥ 3, it's conjectured that n(n+1)···(n+k-1) is NEVER powerful

  Reference: https://erdosproblems.com/137
  Conjectured by: Erdős and Selfridge
  Key paper: Erdős & Selfridge (1975) "The product of consecutive integers is never a power"
-/

import Mathlib

/-!
# Erdős Problem #137: Powerful Products of Consecutive Integers

## Overview

This problem asks about the arithmetic structure of products of consecutive integers.
A **powerful number** is one where every prime factor appears with exponent ≥ 2.

The key insight is that consecutive integers share no common factors (they are
coprime in pairs), so the product of many consecutive integers will have many
"singleton" prime factors (appearing exactly once), preventing it from being powerful.

## Main Results

1. **Definition**: A number n is powerful iff every prime in its factorization
   appears with exponent ≥ 2.

2. **Erdős-Selfridge Theorem** (1975): The product of k ≥ 2 consecutive integers
   is never a perfect power. This is a stronger statement than the powerful question.

3. **Main Conjecture**: For k ≥ 3, the product of k consecutive integers is never
   powerful. This remains open but is widely believed to be true.
-/

namespace Erdos137

open Nat Finset BigOperators

/-! ## Powerful Numbers -/

/--
A natural number n is **powerful** if every prime divisor p of n satisfies p² | n.
Equivalently, in the prime factorization of n, every prime has exponent ≥ 2.
For example: 1, 4, 8, 9, 16, 25, 27, 32, 36, ... are powerful.
-/
def Powerful (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- 1 is powerful (vacuously - no prime divisors). -/
theorem one_powerful : Powerful 1 := by
  constructor
  · exact one_ne_zero
  · intro p hp hdiv
    -- p | 1 implies p = 1, contradicting p.Prime
    exact absurd (Nat.eq_one_of_dvd_one hdiv) hp.ne_one

/-- Perfect squares are powerful. -/
theorem sq_powerful (n : ℕ) (hn : n ≠ 0) : Powerful (n ^ 2) := by
  constructor
  · exact pow_ne_zero 2 hn
  · intro p hp hdiv
    -- If p | n², then p | n (since p is prime)
    have h : p ∣ n := hp.dvd_of_dvd_pow hdiv
    -- So p² | n²
    exact dvd_trans (pow_dvd_pow_of_dvd h 2) (dvd_refl _)

/-- Squarefree numbers > 1 are not powerful (by definition).
    A squarefree number has no repeated prime factors. -/
theorem squarefree_not_powerful (n : ℕ) (hn : n > 1) (hsf : Squarefree n) :
    ¬Powerful n := by
  intro ⟨_, hpow⟩
  -- n > 1 means n has at least one prime factor p
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (_root_.ne_of_gt hn)
  -- By powerful, p² | n
  have hp2 : p ^ 2 ∣ n := hpow p hp hdiv
  -- But squarefree means p * p | n → IsUnit p
  -- Since p is prime, it's not a unit (i.e., p ≠ 1)
  rw [sq] at hp2
  have hunit : IsUnit p := hsf p hp2
  -- IsUnit in ℕ means p = 1, but p is prime so p ≥ 2
  have hp_eq_one : p = 1 := Nat.isUnit_iff.mp hunit
  exact hp.ne_one hp_eq_one

/-! ## Products of Consecutive Integers -/

/-- The product of integers from n+1 to n+k (i.e., k consecutive integers starting after n). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc n (n + k), x

/-- Example: 2 × 3 = 6. -/
example : consecutiveProduct 1 2 = 6 := by native_decide

/-- Example: 2 × 3 × 4 = 24. -/
example : consecutiveProduct 1 3 = 24 := by native_decide

/-- gcd of consecutive integers n and n+1 is 1. -/
theorem consecutive_coprime (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  have h := Nat.coprime_self_add_right (m := n) (n := 1)
  simp only [Nat.coprime_one_right_eq_true, iff_true] at h
  exact h

/-! ## The Erdős-Selfridge Theorem -/

/--
**Erdős-Selfridge Theorem (1975)**:
The product of k ≥ 2 consecutive positive integers is never a perfect power.

That is, if n ≥ 1 and k ≥ 2, then (n+1)(n+2)···(n+k) ≠ m^l for any m and l ≥ 2.

This is axiomatized because the proof requires deep analysis of the prime
factorization structure of consecutive integers and is quite technical.

Reference: P. Erdős, J. L. Selfridge, "The product of consecutive integers
is never a power", Illinois J. Math. 19(2): 292-301, 1975.
-/
axiom erdos_selfridge_theorem :
    ∀ n k : ℕ, n ≥ 1 → k ≥ 2 →
    ∀ m l : ℕ, l ≥ 2 → consecutiveProduct n k ≠ m ^ l

/-- Corollary: Products of consecutive integers are not perfect squares. -/
theorem consecutive_product_not_square (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 2) :
    ∀ m : ℕ, consecutiveProduct n k ≠ m ^ 2 :=
  fun m => erdos_selfridge_theorem n k hn hk m 2 (by norm_num)

/-- Corollary: Products of consecutive integers are not perfect cubes. -/
theorem consecutive_product_not_cube (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 2) :
    ∀ m : ℕ, consecutiveProduct n k ≠ m ^ 3 :=
  fun m => erdos_selfridge_theorem n k hn hk m 3 (by norm_num)

/-! ## The Main Conjecture (Open) -/

/--
**Erdős Conjecture on Powerful Products**:
For k ≥ 3, the product of k consecutive positive integers is never powerful.

This remains an open problem. It is strictly weaker than asking about perfect
powers (since every perfect power is powerful, but not vice versa).

The case k = 2 fails: there are infinitely many n such that n(n+1) is powerful.
For example, if n = 8 then n(n+1) = 72 = 8 × 9 = 2³ × 3², which is powerful.

For k ≥ 3, the conjecture asserts this cannot happen.
-/
def ErdosPowerfulConjecture : Prop :=
  ∀ n k : ℕ, n ≥ 1 → k ≥ 3 → ¬Powerful (consecutiveProduct n k)

/--
We state the expected answer as an axiom.
The conjecture is widely believed to be true but remains unproven.
-/
axiom erdos_powerful_conjecture : ErdosPowerfulConjecture

/-- The main theorem: Erdős Problem #137 (assuming the conjecture). -/
theorem erdos_137 (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 3) :
    ¬Powerful (consecutiveProduct n k) :=
  erdos_powerful_conjecture n k hn hk

/-! ## Counterexample for k = 2 -/

/-- 72 = 8 × 9 = 2³ × 3² is powerful.
    72 = 2³ × 3², and both 2² = 4 | 72 and 3² = 9 | 72. -/
theorem seventy_two_powerful : Powerful 72 := by
  constructor
  · norm_num
  · intro p hp hdiv
    -- 72 = 8 × 9 = 2³ × 3²
    -- Only prime divisors are 2 and 3
    have h72 : (72 : ℕ) = 2^3 * 3^2 := by norm_num
    -- If p | 72 and p is prime, then p ∈ {2, 3}
    have hfact : p = 2 ∨ p = 3 := by
      have hdiv' : p ∣ 2^3 * 3^2 := by rw [← h72]; exact hdiv
      rcases hp.eq_two_or_odd with rfl | _
      · left; rfl
      · right
        have hp3 : p ∣ 3^2 ∨ p ∣ 2^3 := (Nat.Prime.dvd_mul hp).mp hdiv'
        rcases hp3 with h3 | h2
        · -- p divides 3², so p divides 3, so p = 3 (both prime)
          have hp3div : p ∣ 3 := hp.dvd_of_dvd_pow h3
          exact (Nat.dvd_prime Nat.prime_three).mp hp3div |>.resolve_left hp.ne_one
        · have hp2div : p ∣ 2 := hp.dvd_of_dvd_pow h2
          have hp2' := (Nat.dvd_prime Nat.prime_two).mp hp2div |>.resolve_left hp.ne_one
          omega
    rcases hfact with rfl | rfl
    -- p = 2: show 4 | 72
    · norm_num
    -- p = 3: show 9 | 72
    · norm_num

/-- 8 × 9 = 72, showing n(n+1) can be powerful for n = 8. -/
theorem two_consecutive_can_be_powerful :
    ∃ n : ℕ, n ≥ 1 ∧ Powerful (consecutiveProduct n 2) := by
  use 7  -- consecutiveProduct 7 2 = 8 × 9 = 72
  constructor
  · norm_num
  · -- Need to show consecutiveProduct 7 2 = 72
    have h : consecutiveProduct 7 2 = 72 := by native_decide
    rw [h]
    exact seventy_two_powerful

/-! ## Summary

**Problem Status: PARTIALLY SOLVED**

- Erdős-Selfridge (1975): Product of k ≥ 2 consecutive integers is never a perfect power. ✓
- Erdős Conjecture: Product of k ≥ 3 consecutive integers is never powerful. (OPEN)

The powerful conjecture is weaker but remains unproven. The key difficulty is that
powerful numbers form a more complex class than perfect powers.
-/

end Erdos137
