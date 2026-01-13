/-
  Erdős Problem #69: Irrationality of ∑ω(n)/2^n

  Source: https://erdosproblems.com/69
  Status: PROVED (Tao-Teräväinen 2025)

  Statement:
  Is ∑_{n≥2} ω(n)/2^n irrational?

  Where ω(n) counts the number of distinct prime divisors of n.

  Key insight (Tao's observation):
  ∑_{n≥2} ω(n)/2^n = ∑_{p prime} 1/(2^p - 1)

  This reduces Problem 69 to a special case of Problem 257.

  The identity follows from:
  - ω(n) = ∑_{p|n} 1 (sum over prime divisors)
  - Swapping order of summation gives ∑_p ∑_{k≥1} 1/2^(pk)
  - Inner sum is geometric: 1/(2^p - 1)
-/

import Mathlib

open scoped ArithmeticFunction.omega
open BigOperators Finset

namespace Erdos69

/-! ## Definitions -/

/-- The sum of ω(n)/2^n for n ≥ 2 -/
noncomputable def omegaSum : ℝ := ∑' n : ℕ, ω (n + 2) / 2 ^ (n + 2)

/-- The equivalent sum over primes: ∑_p 1/(2^p - 1) -/
noncomputable def primeSum : ℝ := ∑' p : {n : ℕ | n.Prime}, 1 / (2 ^ p.1 - 1 : ℝ)

/-! ## Helper lemmas -/

/-- For any prime p ≥ 2, 2^p > 1 -/
lemma two_pow_gt_one (p : ℕ) (hp : 2 ≤ p) : (2 : ℝ) ^ p > 1 := by
  have h1 : (2 : ℝ) ^ p ≥ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
  have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
  linarith

/-- For any prime p, the geometric series ∑_{k≥1} 1/2^(pk) = 1/(2^p - 1) -/
lemma geometric_sum_over_multiples (p : ℕ) (hp : 2 ≤ p) :
    ∑' k : ℕ, (1 : ℝ) / 2 ^ (p * (k + 1)) = 1 / (2 ^ p - 1) := by
  have h2p : (2 : ℝ) ^ p > 1 := two_pow_gt_one p hp
  have hpos : (2 : ℝ) ^ p - 1 > 0 := by linarith
  have hlt : (1 : ℝ) / 2 ^ p < 1 := by
    rw [div_lt_one (by positivity)]
    exact h2p
  -- Rewrite each term as a power
  have hratio : ∀ k : ℕ, (1 : ℝ) / 2 ^ (p * (k + 1)) = (1 / 2 ^ p) ^ (k + 1) := by
    intro k
    rw [pow_mul, one_div, one_div, inv_pow]
  simp_rw [hratio]
  -- ∑_{k≥0} r^(k+1) = r * ∑_{k≥0} r^k = r * 1/(1-r) = r/(1-r)
  -- For r = 1/2^p: r/(1-r) = (1/2^p)/(1 - 1/2^p) = 1/(2^p - 1)
  have hsum : ∑' k : ℕ, (1 / 2 ^ p : ℝ) ^ k = (1 - 1 / 2 ^ p)⁻¹ :=
    tsum_geometric_of_lt_one (by positivity) hlt
  -- Shift the index: ∑_{k≥0} r^(k+1) = r * ∑_{k≥0} r^k
  calc ∑' k : ℕ, (1 / 2 ^ p : ℝ) ^ (k + 1)
      = ∑' k : ℕ, (1 / 2 ^ p) * (1 / 2 ^ p) ^ k := by
        congr 1; ext k; ring
    _ = (1 / 2 ^ p) * ∑' k : ℕ, (1 / 2 ^ p : ℝ) ^ k := by
        rw [tsum_mul_left]
    _ = (1 / 2 ^ p) * (1 - 1 / 2 ^ p)⁻¹ := by rw [hsum]
    _ = 1 / (2 ^ p - 1) := by field_simp

/-- ω(n) equals the number of primes that divide n -/
lemma omega_eq_card_prime_divisors (n : ℕ) :
    ω n = (n.primeFactors).card := rfl

/-! ## Summability lemmas -/

/-- The sum ∑_n 1/2^n is summable -/
lemma summable_one_div_two_pow : Summable fun n : ℕ => (1 : ℝ) / 2 ^ n := by
  have : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  convert this using 1
  ext n
  simp only [one_div, inv_pow]

/-- The sum ∑_n ω(n)/2^n is summable.
    This follows from comparison with ∑ n/2^n which converges. -/
lemma summable_omega_div_pow : Summable fun n : ℕ => ω n / (2 : ℝ) ^ n := by
  -- ω(n) ≤ log₂(n) ≤ n for all n ≥ 2, so comparison with ∑ n/2^n works
  -- For a full proof, we'd compare with the convergent series ∑ n * (1/2)^n
  sorry

/-- The sum over primes ∑_p 1/(2^p - 1) is summable.
    This follows from comparison with ∑_p 1/2^p (geometric decay). -/
lemma summable_prime_sum : Summable fun p : {n : ℕ | n.Prime} => (1 : ℝ) / (2 ^ p.1 - 1) := by
  -- For p ≥ 2: 1/(2^p - 1) ≤ 2/2^p, and ∑_p 1/2^p converges
  sorry

/-! ## Main identity (Tao's observation) -/

/--
**Tao's Identity**: ∑_{n≥2} ω(n)/2^n = ∑_{p prime} 1/(2^p - 1)

This is the key identity that reduces Erdős Problem 69 to Problem 257.

The proof swaps the order of summation:
  ∑_n ω(n)/2^n = ∑_n (∑_{p|n} 1)/2^n
               = ∑_p ∑_{n: p|n} 1/2^n
               = ∑_p ∑_{k≥1} 1/2^(pk)
               = ∑_p 1/(2^p - 1)
-/
theorem tao_identity : omegaSum = primeSum := by
  -- This requires careful handling of the double sum
  -- and convergence arguments
  sorry

/-! ## Irrationality (from Problem 257) -/

/--
The sum ∑_{p prime} 1/(2^p - 1) is irrational.

This is a special case of Erdős Problem 257, which was proved
unconditionally by Tao and Teräväinen (2025).
-/
theorem primeSum_irrational : Irrational primeSum := by
  -- This follows from Tao-Teräväinen 2025
  -- The proof uses analytic number theory beyond elementary methods
  sorry

/--
**Erdős Problem 69**: ∑_{n≥2} ω(n)/2^n is irrational.

Proved by combining Tao's identity with the irrationality of
the prime sum (Tao-Teräväinen 2025).
-/
theorem erdos_69 : Irrational omegaSum := by
  rw [tao_identity]
  exact primeSum_irrational

end Erdos69
