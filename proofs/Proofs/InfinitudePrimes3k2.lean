import Mathlib

/-!
# Infinitude of Primes congruent to 2 mod 3

We prove there are infinitely many primes congruent to 2 modulo 3 using
an elementary Euclid-style argument (no analytic number theory needed).

This is a special case of Dirichlet's theorem on primes in arithmetic
progressions. The proof mirrors the classical argument for primes ≡ 3 (mod 4).

## The Proof Idea

1. For any n, consider N = 3*(n+1)! - 1
2. N ≡ 2 (mod 3) and N > n
3. The product of integers ≡ 1 (mod 3) is ≡ 1 (mod 3)
4. So N cannot factor entirely into primes ≡ 1 (mod 3) and the prime 3
5. Since 3 does not divide N, at least one prime factor of N is ≡ 2 (mod 3)
6. This prime factor is > n+1 (since all primes ≤ n+1 divide (n+1)!)
-/

namespace InfinitudePrimes3k2

open Nat

/-- Product of two integers ≡ 1 (mod 3) is ≡ 1 (mod 3). -/
lemma mul_mod_three_one {a b : ℕ} (ha : a % 3 = 1) (hb : b % 3 = 1) :
    (a * b) % 3 = 1 := by
  calc (a * b) % 3 = ((a % 3) * (b % 3)) % 3 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 3 := by rw [ha, hb]
    _ = 1 := by norm_num

/-- Product of a list of integers all ≡ 1 (mod 3) is ≡ 1 (mod 3). -/
private lemma list_prod_mod_three_one (l : List ℕ) (h : ∀ x ∈ l, x % 3 = 1) :
    l.prod % 3 = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.prod_cons]
    exact mul_mod_three_one (h a (List.mem_cons_self a t))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- If all prime factors of m (≥ 2) are ≡ 1 (mod 3), then m ≡ 1 (mod 3). -/
private lemma all_factors_one_mod_three {m : ℕ} (hm : m ≥ 2)
    (h : ∀ p, Nat.Prime p → p ∣ m → p % 3 = 1) : m % 3 = 1 := by
  have hm_ne : m ≠ 0 := by omega
  conv_lhs => rw [← Nat.prod_factors hm_ne]
  apply list_prod_mod_three_one
  intro x hx
  exact h x (Nat.prime_of_mem_factors hx) (Nat.dvd_of_mem_factors hx)

/-- Every prime p ≠ 3 satisfies p % 3 = 1 or p % 3 = 2. -/
lemma prime_mod_three {p : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hp0 : p % 3 ≠ 0 := by
    intro heq
    exact hp3 (hp.eq_of_dvd_of_prime Nat.prime_three (Nat.dvd_of_mod_eq_zero heq))
  omega

/-- The candidate number N = 3*(n+1)! - 1 is ≡ 2 (mod 3). -/
lemma candidate_mod_three (n : ℕ) : (3 * (n + 1)! - 1) % 3 = 2 := by
  have h : 3 * (n + 1)! ≥ 1 := by positivity
  omega

/-- The candidate is at least 2. -/
lemma candidate_ge_two (n : ℕ) : 2 ≤ 3 * (n + 1)! - 1 := by
  have h : (n + 1)! ≥ 1 := Nat.one_le_iff_ne_zero.mpr (factorial_ne_zero _)
  omega

/-- If a prime q ≤ n+1 divides 3*(n+1)!-1, then q divides 1, contradiction. -/
lemma prime_factor_large {n q : ℕ} (hq : Nat.Prime q) (hq_le : q ≤ n + 1)
    (hq_dvd : q ∣ (3 * (n + 1)! - 1)) : False := by
  have hq_dvd_fact : q ∣ (n + 1)! := hq.dvd_factorial.mpr hq_le
  have hq_dvd_3fact : q ∣ 3 * (n + 1)! := hq_dvd_fact.mul_left 3
  -- q | 3(n+1)! and q | (3(n+1)!-1), so q | (3(n+1)! - (3(n+1)!-1)) = 1
  have h_ge : 3 * (n + 1)! ≥ 1 := by positivity
  have h_sub : 3 * (n + 1)! - (3 * (n + 1)! - 1) = 1 := by omega
  have hq_dvd_one : q ∣ 1 := h_sub ▸ Nat.dvd_sub' hq_dvd_3fact hq_dvd
  exact absurd (Nat.le_of_dvd one_pos hq_dvd_one) (not_le.mpr hq.one_lt)

/-- For every n, there exists a prime p > n with p ≡ 2 (mod 3). -/
theorem exists_prime_two_mod_three (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 3 = 2 := by
  set N := 3 * (n + 1)! - 1 with hN_def
  have hN_ge : N ≥ 2 := candidate_ge_two n
  have hN_mod : N % 3 = 2 := candidate_mod_three n
  -- By contradiction: assume no prime > n is ≡ 2 (mod 3)
  by_contra h_all
  push_neg at h_all
  -- Then all prime factors of N are ≡ 1 (mod 3)
  have hall : ∀ p, Nat.Prime p → p ∣ N → p % 3 = 1 := by
    intro p hp hpd
    -- p > n+1 (small primes divide (n+1)!, hence 3(n+1)!, can't divide N)
    have hp_large : p > n + 1 := by
      by_contra h_le
      push_neg at h_le
      exact prime_factor_large hp h_le hpd
    -- p ≠ 3 (since 3 does not divide N, as N ≡ 2 mod 3)
    have hp_ne3 : p ≠ 3 := by
      intro rfl
      obtain ⟨k, hk⟩ := hpd
      rw [hk] at hN_mod
      simp [Nat.mul_mod_right] at hN_mod
    -- p % 3 = 1 or 2; if 2, contradicts h_all
    rcases prime_mod_three hp hp_ne3 with h1 | h2
    · exact h1
    · exact absurd h2 (h_all p hp (by omega))
  -- All prime factors ≡ 1 (mod 3) implies N ≡ 1 (mod 3)
  have := all_factors_one_mod_three hN_ge hall
  omega

/-- Infinitude of primes ≡ 2 (mod 3): the set is infinite. -/
theorem infinite_primes_two_mod_three :
    {p : ℕ | Nat.Prime p ∧ p % 3 = 2}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hp, hpn, hpmod⟩ := exists_prime_two_mod_three n
  exact ⟨p, ⟨hp, hpmod⟩, le_of_lt hpn⟩

end InfinitudePrimes3k2
