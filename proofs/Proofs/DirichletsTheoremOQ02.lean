/-
Infinitely Many Primes ≡ 3 (mod 4)

An elementary proof that there are infinitely many primes congruent to 3 modulo 4.
This is a special case of Dirichlet's theorem on primes in arithmetic progressions,
proved using a variant of Euclid's argument without L-functions.

Status: Fully proved (0 sorry, 0 axiom)
-/

import Mathlib

open Finset Nat

namespace DirichletsTheoremOQ02

/-! ## Key lemma: any n ≡ 3 (mod 4) with n > 1 has a prime factor ≡ 3 (mod 4) -/

/-- If n > 1 and n % 4 = 3, then n has a prime factor p with p % 4 = 3.
    Proved by strong induction: if all prime factors were ≡ 1 (mod 4),
    then n ≡ 1 (mod 4), contradicting n ≡ 3 (mod 4). -/
theorem exists_prime_factor_three_mod_four (n : ℕ) (hn : 1 < n) (hmod : n % 4 = 3) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  -- n has a smallest prime factor
  have ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  by_cases hpmod : p % 4 = 3
  · exact ⟨p, hp, hpn, hpmod⟩
  · -- p ≠ 2 (since n is odd: n % 4 = 3 implies n is odd)
    have hn_odd : ¬ 2 ∣ n := by omega
    have hp_ne_2 : p ≠ 2 := fun h => hn_odd (h ▸ hpn)
    -- p is an odd prime with p % 4 ≠ 3, so p % 4 = 1
    have hpmod1 : p % 4 = 1 := by
      have hp_ge := hp.two_le
      have hp_odd : p % 2 = 1 := by
        have := hp.odd_of_ne_two hp_ne_2
        rwa [Nat.odd_iff] at this
      omega
    -- n/p also has a prime factor ≡ 3 (mod 4)
    obtain ⟨k, hk⟩ := hpn
    have hk_gt : 1 < k := by
      rcases k with _ | _ | k
      · simp at hk; omega
      · simp at hk; subst hk; omega
      · omega
    have hk_mod : k % 4 = 3 := by
      have h1 : (p * k) % 4 = 3 := hk ▸ hmod
      rw [Nat.mul_mod, hpmod1] at h1
      simpa using h1
    have hk_lt : k < n := by subst hk; nlinarith [hp.one_lt]
    obtain ⟨q, hq, hqk, hqmod⟩ := exists_prime_factor_three_mod_four k hk_gt hk_mod
    exact ⟨q, hq, dvd_trans hqk ⟨p, by linarith⟩, hqmod⟩
termination_by n
decreasing_by exact hk_lt

/-! ## Main theorem -/

/-- **Main Theorem**: There are infinitely many primes p with p ≡ 3 (mod 4).

Given any n, we construct N = 4·(n+1)! - 1 which satisfies:
- N ≡ 3 (mod 4)
- N > 1
- Any prime factor p of N with p % 4 = 3 satisfies p > n (since p ∤ (n+1)!)
-/
theorem infinite_primes_three_mod_four :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  -- N = 4 * (n+1)! - 1
  set N := 4 * (n + 1).factorial - 1 with hN_def
  have hfac_pos : 0 < (n + 1).factorial := Nat.factorial_pos _
  have hN_gt_one : 1 < N := by simp [N]; omega
  have hN_mod : N % 4 = 3 := by simp [N]; omega
  -- N has a prime factor p with p % 4 = 3
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_factor_three_mod_four N hN_gt_one hN_mod
  refine ⟨p, ⟨hp, hpmod⟩, ?_⟩
  -- Show p > n: if p ≤ n+1 then p | (n+1)!, so p | 4*(n+1)!, so p | N+1
  -- But p | N, so p | gcd(N, N+1) = 1, contradicting p prime
  by_contra h_le
  push_neg at h_le
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fac : p ∣ (n + 1).factorial := hp.dvd_factorial.mpr hp_le
  -- p | 4*(n+1)! = N + 1
  have hp_dvd_Nsucc : p ∣ N + 1 := by
    have : N + 1 = 4 * (n + 1).factorial := by simp [N]; omega
    rw [this]
    exact dvd_mul_of_dvd_right hp_dvd_fac 4
  -- p | N and p | N + 1 is impossible for p ≥ 2
  -- Since p | N and p | (N+1), p | (N+1) - N = 1
  -- p | N and p | (N+1), but gcd(N, N+1) = 1, so p | 1, contradicting primality
  -- p | N and p | N+1 implies p ≤ 1, contradicting primality
  obtain ⟨a, ha⟩ := hpN
  obtain ⟨b, hb⟩ := hp_dvd_Nsucc
  -- p*b = p*a + 1, so p | 1. Since b > a (as p*b > p*a), p*(b-a) ≥ p, but = 1.
  have : p ≤ 1 := by nlinarith [hp.pos, Nat.mul_le_mul_left p (show a + 1 ≤ b by nlinarith)]
  exact absurd this (not_le.mpr hp.one_lt)

/-- The set of primes ≡ 3 (mod 4) is nonempty (3 is such a prime). -/
theorem exists_prime_three_mod_four : ∃ p, Nat.Prime p ∧ p % 4 = 3 :=
  ⟨3, by norm_num, by norm_num⟩

end DirichletsTheoremOQ02
