import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Infinitude of Primes ≡ 2 (mod 3)

## What This Proves

We prove that there are infinitely many primes congruent to 2 modulo 3, using
an elementary Euclid-style argument that requires NO analytic number theory.

This is a special case of Dirichlet's theorem on primes in arithmetic progressions,
but the proof here is completely elementary and was known long before Dirichlet's work.

## The Proof Idea

1. Assume we want to find a prime ≡ 2 (mod 3) greater than any given n
2. Consider N = 3·(n+1)! - 1
3. Observe that N ≡ 2 (mod 3)
4. **Key insight**: The product of integers ≡ 1 (mod 3) is ≡ 1 (mod 3)
5. So N cannot factor entirely into primes ≡ 1 (mod 3) (and 3)
6. Therefore N has at least one prime factor q ≡ 2 (mod 3)
7. But q > n (since q does not divide 3·(n+1)!)
8. So we always find a prime ≡ 2 (mod 3) greater than any n.

## Status
- [x] Complete proof
- [x] No analytic machinery required
- [x] Elementary modular arithmetic only

## Mathlib Dependencies
- `Nat.Prime` : Definition of prime numbers
- `Nat.exists_prime_and_dvd` : Every n ≥ 2 has a prime divisor
- Basic modular arithmetic
-/

namespace InfinitudePrimes3k2

open Nat

/-! ## Key Lemma: Product of 1 (mod 3) integers stays 1 (mod 3) -/

/-- Product of two integers ≡ 1 (mod 3) is ≡ 1 (mod 3) -/
lemma mul_mod_three_one {a b : ℕ} (ha : a % 3 = 1) (hb : b % 3 = 1) :
    (a * b) % 3 = 1 := by
  calc (a * b) % 3 = ((a % 3) * (b % 3)) % 3 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 3 := by rw [ha, hb]
    _ = 1 := by norm_num

/-! ## Key Lemma: Primes other than 3 are either 1 or 2 (mod 3) -/

/-- Every prime ≠ 3 is ≡ 1 or ≡ 2 (mod 3) -/
lemma prime_mod_three {p : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hp_ge2 := hp.two_le
  have hp_mod : p % 3 ≠ 0 := by
    intro h
    have h3_dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := hp.eq_one_or_self_of_dvd 3 h3_dvd
    omega
  omega

/-! ## The Main Theorem -/

/-- If all prime factors of n (other than 3) are ≡ 1 (mod 3), then n % 3 ≠ 2.
    Contrapositive: if n % 3 = 2, then n has a prime factor ≡ 2 (mod 3). -/
lemma factors_determine_mod_three {n : ℕ} (hn : n ≥ 1)
    (h_factors : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 3 ∨ p % 3 = 1) :
    n % 3 ≠ 2 := by
  intro hmod2
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn_ne1 : n ≠ 1 := by omega
    obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd hn_ne1
    have hp_cases := h_factors p hp_prime hp_div
    rcases hp_cases with hp3 | hp1
    · -- Case: p = 3
      -- If 3 | n and n % 3 = 2, contradiction
      have h3_dvd : 3 ∣ n := by rw [hp3] at hp_div; exact hp_div
      have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_dvd
      omega
    · -- Case: p % 3 = 1
      obtain ⟨m, hm⟩ := hp_div
      have hm_pos : m ≥ 1 := by
        by_contra h; push_neg at h
        simp_all
      by_cases hm1 : m = 1
      · simp only [hm1, mul_one] at hm
        omega
      · have hm_ge2 : m ≥ 2 := by omega
        have hp_ge2 : p ≥ 2 := hp_prime.two_le
        have hm_lt : m < n := by
          rw [hm]
          calc m < 2 * m := by omega
            _ ≤ p * m := Nat.mul_le_mul_right m hp_ge2
        have h_m_factors : ∀ q : ℕ, Nat.Prime q → q ∣ m → q = 3 ∨ q % 3 = 1 := by
          intro q hq_prime hq_div
          have hq_div_n : q ∣ n := by rw [hm]; exact dvd_mul_of_dvd_right hq_div p
          exact h_factors q hq_prime hq_div_n
        have hn_eq : n % 3 = (p * m) % 3 := by rw [hm]
        have hmod_prod : (p * m) % 3 = ((p % 3) * (m % 3)) % 3 := Nat.mul_mod p m 3
        rw [hn_eq, hmod_prod, hp1] at hmod2
        simp only [one_mul] at hmod2
        have hm_mod2 : m % 3 = 2 := by omega
        exact ih m hm_lt hm_pos h_m_factors hm_mod2

/-- **Key Lemma**: If n ≡ 2 (mod 3) and n ≥ 2, then n has a prime factor ≡ 2 (mod 3) -/
lemma has_prime_factor_2_mod_3 {n : ℕ} (hn : n ≥ 2) (hmod : n % 3 = 2) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p % 3 = 2 := by
  by_contra hno
  push_neg at hno
  have h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 3 ∨ p % 3 = 1 := by
    intro p hp hdiv
    by_cases hp3 : p = 3
    · left; exact hp3
    · right
      have hmod3 := prime_mod_three hp hp3
      rcases hmod3 with h1 | h2
      · exact h1
      · exfalso; exact hno p hp hdiv h2
  exact factors_determine_mod_three (by omega : n ≥ 1) h hmod

/-- **THE MAIN THEOREM: Infinitely many primes ≡ 2 (mod 3)**

Given any natural number n, there exists a prime p > n with p ≡ 2 (mod 3).
This proves there are infinitely many such primes. -/
theorem infinitely_many_primes_2_mod_3 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 3 = 2 := by
  intro n
  -- Consider N = 3 * (n+1)! - 1
  let N := 3 * (n + 1).factorial - 1
  have hN_mod : N % 3 = 2 := by
    have : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    simp only [N]; omega
  have hN_ge2 : N ≥ 2 := by
    have : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    simp only [N]; omega
  -- N has a prime factor p ≡ 2 (mod 3)
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_2_mod_3 hN_ge2 hN_mod
  use p
  refine ⟨hp_prime, ?_, hp_mod⟩
  -- Show p > n
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_3fact : p ∣ 3 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 3
  have h_ge : 3 * (n + 1).factorial ≥ 1 := by
    have := Nat.factorial_pos (n + 1)
    omega
  have hN_add : N + 1 = 3 * (n + 1).factorial := by omega
  have hp_dvd_diff : p ∣ (N + 1) - N := Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_3fact) hp_div
  simp only [add_tsub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff

/-- Alternative statement: The set of primes ≡ 2 (mod 3) is infinite -/
theorem primes_2_mod_3_infinite : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 3 = 2} := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨n, hn⟩
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_2_mod_3 n
  have hp_mem : p ∈ {q : ℕ | Nat.Prime q ∧ q % 3 = 2} := ⟨hp_prime, hp_mod⟩
  have hp_le : p ≤ n := hn hp_mem
  omega

/-- There is no largest prime ≡ 2 (mod 3) -/
theorem no_largest_prime_2_mod_3 :
    ¬∃ p : ℕ, Nat.Prime p ∧ p % 3 = 2 ∧ ∀ q : ℕ, Nat.Prime q → q % 3 = 2 → q ≤ p := by
  intro ⟨p, _, _, hp_largest⟩
  obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ := infinitely_many_primes_2_mod_3 p
  have hq_le := hp_largest q hq_prime hq_mod
  omega

/-! ## Examples -/

/-- 2 is a prime ≡ 2 (mod 3) -/
example : Nat.Prime 2 ∧ 2 % 3 = 2 := ⟨Nat.prime_two, rfl⟩

/-- 5 is a prime ≡ 2 (mod 3) -/
example : Nat.Prime 5 ∧ 5 % 3 = 2 := ⟨by decide, rfl⟩

/-- 11 is a prime ≡ 2 (mod 3) -/
example : Nat.Prime 11 ∧ 11 % 3 = 2 := ⟨by decide, rfl⟩

/-- 17 is a prime ≡ 2 (mod 3) -/
example : Nat.Prime 17 ∧ 17 % 3 = 2 := ⟨by decide, rfl⟩

/-- 23 is a prime ≡ 2 (mod 3) -/
example : Nat.Prime 23 ∧ 23 % 3 = 2 := ⟨by decide, rfl⟩

#check infinitely_many_primes_2_mod_3
#check primes_2_mod_3_infinite
#check no_largest_prime_2_mod_3

end InfinitudePrimes3k2
