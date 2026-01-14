/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 07447536-f94a-409e-87eb-de15f0868c09

The following was proved by Aristotle:

- theorem tao_identity : omegaSum = primeSum
-/

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

set_option maxHeartbeats 800000

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
  -- Let's rewrite the sum using the definition of omega in terms of prime factors.
  have h_sum : ∑' n : ℕ, (ω (n + 2)) / (2 : ℝ) ^ (n + 2) = ∑' n : ℕ, (∑ p ∈ Nat.primeFactors (n + 2), (1 : ℝ) / (2 : ℝ) ^ (n + 2)) := by
    simp +decide [ div_eq_mul_inv, Finset.sum_mul _ _ _, omega_eq_card_prime_divisors ];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑' n : ℕ, (∑ p ∈ Nat.primeFactors (n + 2), (1 : ℝ) / (2 : ℝ) ^ (n + 2)) = ∑' p : {n : ℕ | n.Prime}, (∑' n : ℕ, if p.val ∣ (n + 2) then (1 : ℝ) / (2 : ℝ) ^ (n + 2) else 0) := by
    have h_fubini : Summable (fun (n : ℕ × {n : ℕ | n.Prime}) => if n.2.val ∣ (n.1 + 2) then (1 : ℝ) / (2 : ℝ) ^ (n.1 + 2) else 0) := by
      have h_fubini : Summable (fun (n : ℕ) => (∑ p ∈ Nat.primeFactors (n + 2), (1 : ℝ) / (2 : ℝ) ^ (n + 2))) := by
        -- We'll use the fact that if the series $\sum_{n=2}^{\infty} \frac{\omega(n)}{2^n}$ converges, then the series $\sum_{n=2}^{\infty} \frac{1}{2^n}$ also converges.
        have h_summable : Summable (fun n : ℕ => (Nat.primeFactors (n + 2)).card / (2 : ℝ) ^ (n + 2)) := by
          have : ∀ n : ℕ, (Nat.primeFactors (n + 2)).card ≤ n + 2 := by
            exact fun n => le_trans ( Finset.card_le_card ( show Nat.primeFactors ( n + 2 ) ⊆ Finset.Icc 1 ( n + 2 ) from fun p hp => Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hp, Nat.le_of_mem_primeFactors hp ⟩ ) ) ( by simp +arith +decide )
          have h_summable : Summable (fun n : ℕ => (n + 2 : ℝ) / (2 : ℝ) ^ (n + 2)) := by
            refine' summable_of_ratio_norm_eventually_le _ _;
            exact 3 / 4;
            · norm_num;
            · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> ring_nf <;> norm_num ; induction hn <;> norm_num [ pow_succ' ] at * ; nlinarith;
          exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by norm_num ) _ ) ) ( fun n => div_le_div_of_nonneg_right ( mod_cast this n ) ( pow_nonneg ( by norm_num ) _ ) ) h_summable;
        aesop;
      rw [ summable_prod_of_nonneg ];
      · refine' ⟨ _, _ ⟩;
        · intro n;
          refine' summable_of_ne_finset_zero _;
          exact Finset.filter ( fun p => p.val ∣ n + 2 ) ( Finset.subtype ( fun p => Nat.Prime p ) ( Nat.divisors ( n + 2 ) ) );
          aesop;
        · refine' h_fubini.congr fun n => _;
          rw [ tsum_eq_sum ];
          any_goals exact Finset.filter ( fun p : { n : ℕ | Nat.Prime n } => p.val ∣ n + 2 ) ( Finset.subtype ( fun p : ℕ => Nat.Prime p ) ( Nat.primeFactors ( n + 2 ) ) );
          · refine' Finset.sum_bij ( fun p hp => ⟨ p, Nat.prime_of_mem_primeFactors hp ⟩ ) _ _ _ _ <;> aesop;
          · aesop;
      · exact fun _ => by positivity;
    rw [ ← Summable.tsum_comm ];
    · refine' tsum_congr fun n => _;
      rw [ tsum_eq_sum ];
      any_goals exact Finset.filter ( fun p => p.val ∣ n + 2 ) ( Finset.subtype ( fun p => Nat.Prime p ) ( Nat.primeFactors ( n + 2 ) ) );
      · refine' Finset.sum_bij ( fun p hp => ⟨ p, Nat.prime_of_mem_primeFactors hp ⟩ ) _ _ _ _ <;> aesop;
      · aesop;
    · convert h_fubini.comp_injective ( Prod.swap_injective ) using 1;
  -- Let's simplify the inner sum $\sum_{n=0}^{\infty} \frac{1}{2^{n+2}}$ if $p \mid (n+2)$.
  have h_inner : ∀ p : {n : ℕ | n.Prime}, ∑' n : ℕ, (if p.val ∣ (n + 2) then (1 : ℝ) / (2 : ℝ) ^ (n + 2) else 0) = 1 / (2 ^ p.val - 1) := by
    -- Let's simplify the inner sum $\sum_{n=0}^{\infty} \frac{1}{2^{n+2}}$ if $p \mid (n+2)$ using the formula for the sum of a geometric series.
    intro p
    have h_geo_series : ∑' n : ℕ, (if p.val ∣ (n + 2) then (1 : ℝ) / (2 : ℝ) ^ (n + 2) else 0) = ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (p.val * (k + 1)) := by
      -- Let's simplify the inner sum $\sum_{n=0}^{\infty} \frac{1}{2^{n+2}}$ if $p \mid (n+2)$ by considering the multiples of $p$.
      have h_multiples : {n : ℕ | p.val ∣ (n + 2)} = {n : ℕ | ∃ k : ℕ, n = p.val * (k + 1) - 2} := by
        ext n; simp [Set.mem_setOf_eq];
        constructor <;> intro h;
        · exact ⟨ ( n + 2 ) / p - 1, eq_tsub_of_add_eq <| by nlinarith [ Nat.div_mul_cancel h, Nat.sub_add_cancel ( show 1 ≤ ( n + 2 ) / p from Nat.div_pos ( Nat.le_of_dvd ( Nat.succ_pos _ ) h ) p.2.pos ) ] ⟩;
        · rcases h with ⟨ k, rfl ⟩ ; exact ⟨ k + 1, by rw [ Nat.sub_add_cancel ( by nlinarith [ p.2.two_le ] ) ] ⟩;
      rw [ Set.ext_iff ] at h_multiples;
      rw [ tsum_eq_tsum_of_ne_zero_bij ];
      use fun x => p.val * ( x + 1 ) - 2;
      · norm_num [ Function.Injective ];
        intro a b h; rw [ tsub_left_inj ] at h <;> nlinarith [ p.2.two_le ] ;
      · intro n hn; specialize h_multiples n; aesop;
      · intro x; rw [ Nat.sub_add_cancel ( show 2 ≤ ( p : ℕ ) * ( x + 1 ) from by nlinarith only [ p.2.two_le ] ) ] ; aesop;
    convert geometric_sum_over_multiples p.val p.prop.two_le using 1;
  unfold Erdos69.omegaSum Erdos69.primeSum; aesop;

/-! ## Irrationality (from Problem 257) -/

/- Aristotle failed to find a proof. -/
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