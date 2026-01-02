import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Infinitude of Primes ≡ 3 (mod 4)

## What This Proves

We prove that there are infinitely many primes congruent to 3 modulo 4, using
an elementary Euclid-style argument that requires NO analytic number theory.

This is a special case of Dirichlet's theorem on primes in arithmetic progressions,
but the proof here is completely elementary and was known long before Dirichlet's work.

## The Proof Idea

1. Assume there are only finitely many primes ≡ 3 (mod 4): say p₁, p₂, ..., pₖ
2. Consider N = 4·(n+1)! - 1
3. Observe that N ≡ 3 (mod 4)
4. **Key insight**: The product of integers ≡ 1 (mod 4) is ≡ 1 (mod 4)
5. So N cannot factor entirely into primes ≡ 1 (mod 4) (and 2)
6. Therefore N has at least one prime factor q ≡ 3 (mod 4)
7. But q > n (since q does not divide 4·(n+1)!)
8. So we always find a prime ≡ 3 (mod 4) greater than any n.

## Status
- [x] Complete proof
- [x] No analytic machinery required
- [x] Elementary modular arithmetic only

## Mathlib Dependencies
- `Nat.Prime` : Definition of prime numbers
- `Nat.exists_prime_and_dvd` : Every n ≥ 2 has a prime divisor
- Basic modular arithmetic
-/

namespace InfinitudePrimes4k3

open Nat

/-! ## Key Lemma: Product of 1 (mod 4) integers stays 1 (mod 4) -/

/-- Product of two integers ≡ 1 (mod 4) is ≡ 1 (mod 4) -/
lemma mul_mod_four_one {a b : ℕ} (ha : a % 4 = 1) (hb : b % 4 = 1) :
    (a * b) % 4 = 1 := by
  calc (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 4 := by rw [ha, hb]
    _ = 1 := by norm_num

/-! ## Key Lemma: Odd primes are either 1 or 3 (mod 4) -/

/-- Every odd prime is ≡ 1 or ≡ 3 (mod 4) -/
lemma prime_mod_four {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  have hk4 : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
  rcases hk4 with heven | hodd_k
  · -- k is even, so k = 2m, and p = 2(2m) + 1 = 4m + 1 ≡ 1 (mod 4)
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero heven
    left
    calc p % 4 = (2 * k + 1) % 4 := by rw [hk]
      _ = (2 * (2 * m) + 1) % 4 := by rw [hm]
      _ = (4 * m + 1) % 4 := by ring_nf
      _ = 1 := by omega
  · -- k is odd, so k = 2m + 1, and p = 2(2m+1) + 1 = 4m + 3 ≡ 3 (mod 4)
    obtain ⟨m, hm⟩ := Nat.odd_iff.mpr hodd_k
    right
    calc p % 4 = (2 * k + 1) % 4 := by rw [hk]
      _ = (2 * (2 * m + 1) + 1) % 4 := by rw [hm]
      _ = (4 * m + 3) % 4 := by ring_nf
      _ = 3 := by omega

/-! ## The Main Theorem -/

/-- If all odd prime factors of n are ≡ 1 (mod 4), then n % 4 ≠ 3.
    Contrapositive: if n % 4 = 3, then n has an odd prime factor ≡ 3 (mod 4). -/
lemma factors_determine_mod_four {n : ℕ} (hn : n ≥ 1)
    (h_factors : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 2 ∨ p % 4 = 1) :
    n % 4 ≠ 3 := by
  intro hmod3
  -- We'll use induction on the number of factors
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- n ≥ 1 and n % 4 = 3, so n ≥ 3
    have hn3 : n ≥ 3 := by omega
    -- n has a prime factor p
    have hn_ne1 : n ≠ 1 := by omega
    obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd hn_ne1
    -- p = 2 or p % 4 = 1
    have hp_cases := h_factors p hp_prime hp_div
    rcases hp_cases with hp2 | hp1
    · -- Case: p = 2
      -- If 2 | n and n % 4 = 3, we get a contradiction
      -- because n % 4 = 3 means n is odd
      have h2_dvd : 2 ∣ n := by rw [hp2] at hp_div; exact hp_div
      -- n % 4 = 3 means n % 2 = 1 (odd)
      -- But 2 | n means n % 2 = 0 (even)
      have hn_mod2 : n % 2 = 1 := by omega
      have h2_mod2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2_dvd
      omega
    · -- Case: p % 4 = 1
      -- Then n = p * m for some m ≥ 1
      obtain ⟨m, hm⟩ := hp_div
      -- If m = 0, then n = 0, contradiction with hn
      have hm_pos : m ≥ 1 := by
        by_contra h; push_neg at h
        simp_all
      -- If m = 1, then n = p, so p % 4 = n % 4 = 3, but p % 4 = 1, contradiction
      by_cases hm1 : m = 1
      · simp only [hm1, mul_one] at hm
        omega
      · -- m > 1, so m < n
        have hm_ge2 : m ≥ 2 := by omega
        have hp_ge2 : p ≥ 2 := hp_prime.two_le
        have hm_lt : m < n := by
          rw [hm]
          calc m < 2 * m := by omega
            _ ≤ p * m := by omega
        -- m also has all prime factors = 2 or ≡ 1 (mod 4)
        have h_m_factors : ∀ q : ℕ, Nat.Prime q → q ∣ m → q = 2 ∨ q % 4 = 1 := by
          intro q hq_prime hq_div
          have hq_div_n : q ∣ n := by rw [hm]; exact dvd_mul_of_dvd_right hq_div p
          exact h_factors q hq_prime hq_div_n
        -- Compute n % 4 in terms of p % 4 and m % 4
        have hn_eq : n % 4 = (p * m) % 4 := by rw [hm]
        have hmod_prod : (p * m) % 4 = ((p % 4) * (m % 4)) % 4 := Nat.mul_mod p m 4
        rw [hn_eq, hmod_prod, hp1] at hmod3
        simp only [one_mul] at hmod3
        -- So m % 4 = 3
        have hm_mod3 : m % 4 = 3 := by omega
        -- Apply IH to m
        have hm_ge1 : m ≥ 1 := hm_pos
        exact ih m hm_lt hm_ge1 h_m_factors hm_mod3

/-- **Key Lemma**: If n ≡ 3 (mod 4) and n ≥ 3, then n has a prime factor ≡ 3 (mod 4) -/
lemma has_prime_factor_3_mod_4 {n : ℕ} (hn : n ≥ 3) (hmod : n % 4 = 3) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  by_contra hno
  push_neg at hno
  -- All prime factors are either 2 or ≡ 1 (mod 4)
  have h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 2 ∨ p % 4 = 1 := by
    intro p hp hdiv
    by_cases hp2 : p = 2
    · left; exact hp2
    · right
      have hmod4 := prime_mod_four hp hp2
      rcases hmod4 with h1 | h3
      · exact h1
      · exfalso; exact hno p hp hdiv h3
  -- But then n % 4 ≠ 3, contradiction
  exact factors_determine_mod_four (by omega : n ≥ 1) h hmod

/-- **THE MAIN THEOREM: Infinitely many primes ≡ 3 (mod 4)**

Given any natural number n, there exists a prime p > n with p ≡ 3 (mod 4).
This proves there are infinitely many such primes. -/
theorem infinitely_many_primes_3_mod_4 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 4 = 3 := by
  intro n
  -- Consider N = 4 * (n+1)! - 1
  -- This ensures N > n and N ≡ 3 (mod 4)
  let N := 4 * (n + 1).factorial - 1
  have hN_mod : N % 4 = 3 := by
    have h1 : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    have h2 : 4 * (n + 1).factorial ≥ 4 := by omega
    simp only [N]
    omega
  have hN_ge3 : N ≥ 3 := by
    have h1 : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    simp only [N]
    omega
  -- N has a prime factor p ≡ 3 (mod 4)
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  use p
  refine ⟨hp_prime, ?_, hp_mod⟩
  -- Show p > n
  by_contra hpn
  push_neg at hpn
  -- If p ≤ n, then p ≤ n + 1, so p ∣ (n+1)!
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := by
    exact Nat.dvd_factorial hp_prime.pos hp_le
  -- So p ∣ 4 * (n+1)!
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  -- But p ∣ N = 4 * (n+1)! - 1
  -- So p ∣ 4 * (n+1)! - N = 1
  have hp_dvd_1 : p ∣ 1 := by
    have hN_eq : N = 4 * (n + 1).factorial - 1 := rfl
    have h_ge : 4 * (n + 1).factorial ≥ 1 := by
      have := Nat.factorial_pos (n + 1)
      omega
    have hN_add : N + 1 = 4 * (n + 1).factorial := by omega
    have : p ∣ (N + 1) - N := Nat.dvd_sub' (by rw [hN_add]; exact hp_dvd_4fact) hp_div
    simp at this
    exact this
  -- But p is prime, so p ≥ 2, contradiction
  have : p = 1 := Nat.dvd_one.mp hp_dvd_1
  exact hp_prime.ne_one this

/-- Alternative statement: The set of primes ≡ 3 (mod 4) is infinite -/
theorem primes_3_mod_4_infinite : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} := by
  rw [Set.infinite_iff_nat_lt]
  intro n
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_3_mod_4 n
  exact ⟨p, ⟨hp_prime, hp_mod⟩, hp_gt⟩

/-- There is no largest prime ≡ 3 (mod 4) -/
theorem no_largest_prime_3_mod_4 :
    ¬∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ ∀ q : ℕ, Nat.Prime q → q % 4 = 3 → q ≤ p := by
  intro ⟨p, _, _, hp_largest⟩
  obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ := infinitely_many_primes_3_mod_4 p
  have hq_le := hp_largest q hq_prime hq_mod
  omega

/-! ## Examples -/

/-- 3 is the smallest prime ≡ 3 (mod 4) -/
example : Nat.Prime 3 ∧ 3 % 4 = 3 := ⟨Nat.prime_three, rfl⟩

/-- 7 is a prime ≡ 3 (mod 4) -/
example : Nat.Prime 7 ∧ 7 % 4 = 3 := ⟨by decide, rfl⟩

/-- 11 is a prime ≡ 3 (mod 4) -/
example : Nat.Prime 11 ∧ 11 % 4 = 3 := ⟨by decide, rfl⟩

/-- 19 is a prime ≡ 3 (mod 4) -/
example : Nat.Prime 19 ∧ 19 % 4 = 3 := ⟨by decide, rfl⟩

/-- 23 is a prime ≡ 3 (mod 4) -/
example : Nat.Prime 23 ∧ 23 % 4 = 3 := ⟨by decide, rfl⟩

#check infinitely_many_primes_3_mod_4
#check primes_3_mod_4_infinite
#check no_largest_prime_3_mod_4

end InfinitudePrimes4k3
