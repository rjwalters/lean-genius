import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Infinitude of Primes ≡ 1 (mod 4)

## What This Proves

We prove that there are infinitely many primes congruent to 1 modulo 4, using
an elementary argument based on Fermat's theorem on sums of two squares.

This is a special case of Dirichlet's theorem on primes in arithmetic progressions,
but the proof here requires NO analytic number theory.

## The Proof Idea

1. Given any n, consider N = (2 · (n+1)!)² + 1
2. N is odd (sum of even² and 1) and N > 1, so N has odd prime factors
3. **Key insight**: If an odd prime p divides k² + 1, then -1 is a square mod p
4. By Euler's criterion: -1 is a square mod p iff p ≡ 1 (mod 4)
5. Therefore every odd prime factor of N is ≡ 1 (mod 4)
6. At least one prime factor p > n (since p ∤ (n+1)! when p > n+1)
7. So we always find a prime ≡ 1 (mod 4) greater than any n.

## Status
- [x] Complete proof
- [x] No analytic machinery required
- [x] Uses Mathlib's Fermat two-squares infrastructure

## Mathlib Dependencies
- `Nat.Prime` : Definition of prime numbers
- `Nat.exists_prime_and_dvd` : Every n ≥ 2 has a prime divisor
- `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` : Key lemma from SumTwoSquares
- Basic modular arithmetic
-/

namespace InfinitudePrimes4k1

open Nat

/-! ## Key Lemma: Odd primes dividing k² + 1 are ≡ 1 (mod 4) -/

/-- If a prime p divides k² + 1 and p ≠ 2, then p ≡ 1 (mod 4).
    This follows because -1 is a square mod p iff p ≡ 1 (mod 4). -/
lemma prime_dvd_sq_add_one_mod_four {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hdiv : p ∣ k ^ 2 + 1) : p % 4 = 1 := by
  -- -1 is a square mod p because k² ≡ -1 (mod p)
  have hsq : IsSquare (-1 : ZMod p) := by
    use (k : ZMod p)
    -- k² + 1 ≡ 0 (mod p), so k² ≡ -1 (mod p)
    have hzero : ((k ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact hdiv
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hzero
    -- From k² + 1 = 0, we get k² = -1
    have h : (k : ZMod p) ^ 2 = -1 := by
      have : (k : ZMod p) ^ 2 + 1 = 0 := hzero
      calc (k : ZMod p) ^ 2 = (k : ZMod p) ^ 2 + 1 - 1 := by ring
        _ = 0 - 1 := by rw [this]
        _ = -1 := by ring
    rw [sq] at h
    exact h.symm
  -- Apply the key lemma from Mathlib
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne3 := Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one hp (dvd_refl p) hsq
  -- p % 4 ∈ {0, 1, 2, 3}, p is odd prime, so p % 4 ∈ {1, 3}
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨m, hm⟩ := hodd
    have : p ≥ 3 := by have := hp.two_le; omega
    omega
  rcases hmod with h1 | h3
  · exact h1
  · exact absurd h3 hne3

/-- An odd number greater than 1 has an odd prime factor -/
lemma exists_odd_prime_factor {n : ℕ} (hn : n > 1) (hodd : Odd n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p ≠ 2 := by
  obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  use p, hp_prime, hp_div
  intro hp2
  rw [hp2] at hp_div
  have : Even n := even_iff_two_dvd.mpr hp_div
  exact (Nat.odd_iff_not_even.mp hodd) this

/-! ## The Main Theorem -/

/-- **THE MAIN THEOREM: Infinitely many primes ≡ 1 (mod 4)**

Given any natural number n, there exists a prime p > n with p ≡ 1 (mod 4).
This proves there are infinitely many such primes. -/
theorem infinitely_many_primes_1_mod_4 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 4 = 1 := by
  intro n
  -- Consider N = (2 * (n+1)!)² + 1
  let N := (2 * (n + 1).factorial) ^ 2 + 1
  -- N is odd (even² + 1)
  have hN_odd : Odd N := by
    simp only [N]
    have heven : Even ((2 * (n + 1).factorial) ^ 2) := by
      apply Even.pow_of_ne_zero
      exact even_two_mul _
      omega
    exact heven.add_one
  -- N > 1
  have hN_gt1 : N > 1 := by
    simp only [N]
    have h1 : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    have h2 : (2 * (n + 1).factorial) ^ 2 ≥ 4 := by nlinarith
    omega
  -- N has an odd prime factor
  obtain ⟨p, hp_prime, hp_div, hp_ne2⟩ := exists_odd_prime_factor hN_gt1 hN_odd
  use p
  refine ⟨hp_prime, ?_, ?_⟩
  -- Show p > n
  · by_contra hpn
    push_neg at hpn
    -- If p ≤ n, then p ≤ n + 1, so p ∣ (n+1)!
    have hp_le : p ≤ n + 1 := by omega
    have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
    -- So p ∣ 2 * (n+1)!
    have hp_dvd_2fact : p ∣ 2 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
    -- So p ∣ (2 * (n+1)!)²
    have hp_dvd_sq : p ∣ (2 * (n + 1).factorial) ^ 2 := by
      rw [sq]
      exact dvd_mul_of_dvd_left hp_dvd_2fact _
    -- But p ∣ N = (2 * (n+1)!)² + 1
    -- So p ∣ N - (2 * (n+1)!)² = 1
    have hp_dvd_diff : p ∣ N - (2 * (n + 1).factorial) ^ 2 := Nat.dvd_sub' hp_div hp_dvd_sq
    -- N - (2*(n+1)!)² = (2*(n+1)!)² + 1 - (2*(n+1)!)² = 1
    have hN_sub : N - (2 * (n + 1).factorial) ^ 2 = 1 := by simp only [N]; omega
    rw [hN_sub] at hp_dvd_diff
    -- p ∣ 1 but p is prime, contradiction
    exact hp_prime.not_dvd_one hp_dvd_diff
  -- Show p ≡ 1 (mod 4)
  · exact prime_dvd_sq_add_one_mod_four hp_prime hp_ne2 hp_div

/-- Alternative statement: The set of primes ≡ 1 (mod 4) is infinite -/
theorem primes_1_mod_4_infinite : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 1} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_1_mod_4 n
  exact ⟨p, ⟨hp_prime, hp_mod⟩, hp_gt⟩

/-- There is no largest prime ≡ 1 (mod 4) -/
theorem no_largest_prime_1_mod_4 :
    ¬∃ p : ℕ, Nat.Prime p ∧ p % 4 = 1 ∧ ∀ q : ℕ, Nat.Prime q → q % 4 = 1 → q ≤ p := by
  intro ⟨p, _, _, hp_largest⟩
  obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ := infinitely_many_primes_1_mod_4 p
  have hq_le := hp_largest q hq_prime hq_mod
  omega

/-! ## Examples -/

/-- 5 is a prime ≡ 1 (mod 4) -/
example : Nat.Prime 5 ∧ 5 % 4 = 1 := ⟨by decide, rfl⟩

/-- 13 is a prime ≡ 1 (mod 4) -/
example : Nat.Prime 13 ∧ 13 % 4 = 1 := ⟨by decide, rfl⟩

/-- 17 is a prime ≡ 1 (mod 4) -/
example : Nat.Prime 17 ∧ 17 % 4 = 1 := ⟨by decide, rfl⟩

/-- 29 is a prime ≡ 1 (mod 4) -/
example : Nat.Prime 29 ∧ 29 % 4 = 1 := ⟨by decide, rfl⟩

/-- 37 is a prime ≡ 1 (mod 4) -/
example : Nat.Prime 37 ∧ 37 % 4 = 1 := ⟨by decide, rfl⟩

#check infinitely_many_primes_1_mod_4
#check primes_1_mod_4_infinite
#check no_largest_prime_1_mod_4

end InfinitudePrimes4k1
