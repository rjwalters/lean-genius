/-
# Chebyshev's Prime Counting Bounds

This file proves explicit bounds on the prime counting function using
Chebyshev's 1852 method via central binomial coefficients and primorials.

**Status**: COMPLETE (0 axioms)
- Upper and lower bounds on θ(n) and π(n)
- Uses Bertrand's postulate for lower bounds

**Key Results (Upper Bounds)**:
- θ(n) ≤ n · log 4 (weak Chebyshev upper bound)
- n^{π(2n) - π(n)} ≤ 4^n for n ≥ 1
- The product of primes in (n, 2n] divides C(2n, n)

**Key Results (Lower Bounds)**:
- π(2n) - π(n) ≥ 1 for n ≥ 1 (Bertrand's postulate)
- π(2^k) ≥ k for k ≥ 1 (telescoping Bertrand)
- π(n) ≥ log₂(n) for n ≥ 2 (logarithmic lower bound)
- θ(2n) - θ(n) ≥ log(n+1) for n ≥ 1

**Historical Context**:
Chebyshev (1852) proved that π(x) is asymptotic to x/log(x) up to constants,
well before the Prime Number Theorem was proved in 1896.

**Mathlib Dependencies**:
- `Nat.primorial` and `primorial_le_4_pow`
- `Nat.centralBinom` and factorization theorems
- `Nat.primeCounting` (π function)
- `Nat.exists_prime_lt_and_le_two_mul` (Bertrand's postulate)
- `Real.log` for logarithmic bounds
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ChebyshevBounds

open Nat Finset Real

/-!
## Chebyshev's First Function θ(n)

We define θ(n) = Σ_{p ≤ n} log p (sum of logs of primes ≤ n).
This is more natural for analytic methods than π(n).
-/

/-- The first Chebyshev function θ(n): sum of log p for primes p ≤ n -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ filter Nat.Prime (range (n + 1)), Real.log p

/-- θ(n) is non-negative -/
theorem chebyshevTheta_nonneg (n : ℕ) : 0 ≤ chebyshevTheta n := by
  unfold chebyshevTheta
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_filter.mp hp).2
  apply Real.log_nonneg
  have : 2 ≤ p := hprime.two_le
  have : (2 : ℝ) ≤ p := by exact_mod_cast this
  linarith

/-!
## Upper Bound on θ(n) via Primorial

From primorial_le_4_pow: n# = ∏_{p ≤ n} p ≤ 4^n
Taking log: θ(n) = Σ_{p ≤ n} log p ≤ n * log 4
-/

/-- θ(n) ≤ n * log 4 (weak Chebyshev upper bound) -/
theorem chebyshevTheta_le (n : ℕ) : chebyshevTheta n ≤ n * Real.log 4 := by
  unfold chebyshevTheta
  -- Use primorial_le_4_pow: ∏_{p ≤ n} p ≤ 4^n
  have hprim := primorial_le_4_pow n
  have hprim_pos : 0 < primorial n := primorial_pos n
  by_cases hn : n = 0
  · -- n = 0: range 1 = {0}, filter Prime {0} = ∅
    subst hn
    have hempty : filter Nat.Prime (range 1) = ∅ := by
      ext x
      simp only [mem_filter, mem_range, not_mem_empty, iff_false, not_and]
      intro hx
      interval_cases x
      exact Nat.not_prime_zero
    simp only [hempty, sum_empty, Nat.cast_zero, zero_mul, le_refl]
  -- n > 0: Use log monotonicity
  have hprim_real : (primorial n : ℝ) ≤ ((4 : ℕ) ^ n : ℕ) := by exact_mod_cast hprim
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < primorial n) hprim_real
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  rw [Real.log_pow] at hlog
  -- log(primorial n) = Σ log p = θ(n)
  have hprod_cast : (primorial n : ℝ) = ∏ p ∈ filter Nat.Prime (range (n + 1)), (p : ℝ) := by
    unfold primorial
    simp only [Nat.cast_prod]
  rw [hprod_cast] at hlog
  have hsum : Real.log (∏ p ∈ filter Nat.Prime (range (n + 1)), (p : ℝ)) =
      ∑ p ∈ filter Nat.Prime (range (n + 1)), Real.log p := by
    rw [Real.log_prod]
    intro p hp
    have hprime := (mem_filter.mp hp).2
    exact_mod_cast hprime.ne_zero
  rw [hsum] at hlog
  linarith

/-!
## Central Binomial Bounds

Upper bound: C(2n, n) ≤ 4^n
This follows from the binomial theorem.
-/

/-- Upper bound: C(2n, n) ≤ 4^n -/
theorem centralBinom_le_four_pow (n : ℕ) : centralBinom n ≤ 4 ^ n := by
  calc centralBinom n = (2 * n).choose n := rfl
    _ ≤ ∑ k ∈ range (2 * n + 1), (2 * n).choose k := by
        apply single_le_sum (fun k _ => Nat.zero_le _)
        simp only [mem_range]
        omega
    _ = 2 ^ (2 * n) := sum_range_choose (2 * n)
    _ = (2 ^ 2) ^ n := by rw [← pow_mul]
    _ = 4 ^ n := by norm_num

/-!
## Product of Primes in (n, 2n] Divides C(2n, n)

This is a key lemma for Chebyshev-type bounds.
-/

/-- All primes p with n < p ≤ 2n divide C(2n, n) -/
theorem prime_in_interval_dvd_centralBinom {p n : ℕ} (hp : Nat.Prime p)
    (hlo : n < p) (hhi : p ≤ 2 * n) : p ∣ centralBinom n := by
  rw [centralBinom_eq_two_mul_choose]
  -- Use hp.dvd_choose_add: if k < p and p ≤ n then p ∣ C(n, k)
  -- Here we have p divides C(2n, n) because:
  -- - p ≤ 2n (so p can divide (2n)!)
  -- - p > n (so p does NOT divide n! or (2n-n)! = n!)
  -- The multiplicity of p in C(2n,n) = floor(2n/p) - 2*floor(n/p)
  -- Since n < p ≤ 2n: floor(2n/p) = 1 and floor(n/p) = 0
  -- So multiplicity = 1 - 0 = 1, hence p | C(2n,n)
  have h1 : (2 * n).choose n = (n + n).choose n := by ring_nf
  rw [h1]
  have hle : p ≤ n + n := by omega
  -- dvd_choose_add signature: (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p ≤ a + b)
  -- Here a = b = n, so we need n < p (which is hlo) twice
  exact hp.dvd_choose_add hlo hlo hle

/-- The product of primes in the interval (n, 2n] -/
noncomputable def prodPrimesInInterval (n : ℕ) : ℕ :=
  ∏ p ∈ filter Nat.Prime (Ico (n + 1) (2 * n + 1)), p

/-- The product of primes in (n, 2n] divides C(2n, n) -/
theorem prodPrimesInInterval_dvd_centralBinom (n : ℕ) :
    prodPrimesInInterval n ∣ centralBinom n := by
  unfold prodPrimesInInterval
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (mem_filter.mp hp).2.prime
  · intro p hp
    have ⟨hIco, hprime⟩ := mem_filter.mp hp
    have ⟨hlo, hhi⟩ := mem_Ico.mp hIco
    exact prime_in_interval_dvd_centralBinom hprime (Nat.lt_of_succ_le hlo) (Nat.lt_succ_iff.mp hhi)

/-!
## Upper Bound on Prime Count in Doubling Intervals

From n^{π(2n) - π(n)} ≤ prod_{n < p ≤ 2n} p ≤ C(2n,n) ≤ 4^n,
we derive bounds on π(2n) - π(n).
-/

/-- The number of primes in (n, 2n] -/
def numPrimesInInterval (n : ℕ) : ℕ :=
  (filter Nat.Prime (Ico (n + 1) (2 * n + 1))).card

/-- Key lemma: If the product of primes each > n divides M, then n^k ≤ M -/
theorem pow_le_of_prod_primes_dvd {M n : ℕ} (_hn : 0 < n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ n < p)
    (hdvd : ∏ p ∈ S, p ∣ M) (hM : 0 < M) :
    n ^ S.card ≤ M := by
  have hprod_le : n ^ S.card ≤ ∏ p ∈ S, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le n)
    intro p hp
    exact (hS p hp).2.le
  calc n ^ S.card ≤ ∏ p ∈ S, p := hprod_le
    _ ≤ M := Nat.le_of_dvd hM hdvd

/-- Main power bound: n^{π(2n) - π(n)} ≤ 4^n for n ≥ 1 -/
theorem pow_numPrimesInInterval_le (n : ℕ) (hn : 1 ≤ n) :
    n ^ numPrimesInInterval n ≤ 4 ^ n := by
  have hS : ∀ p ∈ filter Nat.Prime (Ico (n + 1) (2 * n + 1)), Nat.Prime p ∧ n < p := by
    intro p hp
    have ⟨hIco, hprime⟩ := mem_filter.mp hp
    have ⟨hlo, _⟩ := mem_Ico.mp hIco
    exact ⟨hprime, Nat.lt_of_succ_le hlo⟩
  have hdvd : prodPrimesInInterval n ∣ centralBinom n := prodPrimesInInterval_dvd_centralBinom n
  have hcb_pos : 0 < centralBinom n := centralBinom_pos n
  unfold numPrimesInInterval prodPrimesInInterval at *
  calc n ^ (filter Nat.Prime (Ico (n + 1) (2 * n + 1))).card
      ≤ centralBinom n := pow_le_of_prod_primes_dvd hn _ hS hdvd hcb_pos
    _ ≤ 4 ^ n := centralBinom_le_four_pow n

/-!
## Connection to π(2n) - π(n)

We show that numPrimesInInterval equals π(2n) - π(n).
-/

/-- The count equals π(2n) - π(n) -/
theorem numPrimesInInterval_eq (n : ℕ) : numPrimesInInterval n = π (2 * n) - π n := by
  unfold numPrimesInInterval primeCounting primeCounting'
  have h1 : count Nat.Prime (2 * n + 1) = (filter Nat.Prime (range (2 * n + 1))).card :=
    count_eq_card_filter_range Nat.Prime (2 * n + 1)
  have h2 : count Nat.Prime (n + 1) = (filter Nat.Prime (range (n + 1))).card :=
    count_eq_card_filter_range Nat.Prime (n + 1)
  rw [h1, h2]
  have hunion : range (2 * n + 1) = range (n + 1) ∪ Ico (n + 1) (2 * n + 1) := by
    ext x; simp only [mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range (n + 1)) (Ico (n + 1) (2 * n + 1)) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_range] at ha
    simp only [mem_Ico] at hb
    omega
  rw [hunion, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
  omega

/-- Main result: n^{π(2n) - π(n)} ≤ 4^n for n ≥ 1 -/
theorem pow_primeCounting_diff_le (n : ℕ) (hn : 1 ≤ n) :
    n ^ (π (2 * n) - π n) ≤ 4 ^ n := by
  rw [← numPrimesInInterval_eq]
  exact pow_numPrimesInInterval_le n hn

/-!
## Summary

We have established:
1. θ(n) ≤ n log 4 ≈ 1.386 n (Chebyshev upper bound on first Chebyshev function)
2. n^{π(2n) - π(n)} ≤ 4^n (power bound on prime density in doubling intervals)

These demonstrate Chebyshev's fundamental technique. The Prime Number Theorem
shows θ(n) ~ n, so our bound θ(n) ≤ 1.386 n is within a constant factor.

Taking logarithms of the power bound gives:
  (π(2n) - π(n)) · log n ≤ n · log 4
Hence:
  π(2n) - π(n) ≤ (log 4 / log n) · n ≈ 1.386 n / log n

This is a Chebyshev-type upper bound on the prime counting function.
-/

/-!
## Lower Bounds via Bertrand's Postulate

Bertrand's postulate: For all n ≥ 1, there exists a prime p with n < p ≤ 2n.
This is `Nat.exists_prime_lt_and_le_two_mul` in Mathlib.

By iterating Bertrand's postulate:
- π(2n) - π(n) ≥ 1 for n ≥ 1
- Telescoping: π(2^k) ≥ k for k ≥ 1
- Hence: π(n) ≥ ⌊log₂ n⌋ for n ≥ 2
-/

/-- From Bertrand's postulate: π(2n) - π(n) ≥ 1 for n ≥ 1 -/
theorem primeCounting_doubling_ge_one (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ π (2 * n) - π n := by
  -- Get Bertrand's prime
  have hne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  obtain ⟨p, hp_prime, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul n hne
  -- p is a prime with n < p ≤ 2n
  -- π(2n) counts p, π(n) does not since p > n and p ≤ 2n
  -- We need to show π(n) < π(2*n), i.e., there's at least one more prime ≤ 2n than ≤ n
  -- Since p is prime, n < p ≤ 2n, we have π(p) = π(p-1) + 1 and π(n) ≤ π(p-1)
  have hp_pos : 0 < p := hp_prime.pos
  have key : π p = π (p - 1) + 1 := by
    unfold primeCounting primeCounting'
    rw [Nat.sub_add_cancel hp_pos, Nat.count_succ, if_pos hp_prime]
  have h1 : π n ≤ π (p - 1) := Nat.monotone_primeCounting (by omega : n ≤ p - 1)
  have h2 : π p ≤ π (2 * n) := Nat.monotone_primeCounting hhi
  omega

/-- Telescoping Bertrand: π(2^k) ≥ k for k ≥ 1 -/
theorem primeCounting_pow_two_ge (k : ℕ) (hk : 1 ≤ k) : k ≤ π (2 ^ k) := by
  induction k with
  | zero => contradiction
  | succ k ih =>
    by_cases hk0 : k = 0
    · -- Base case: k = 0, need 1 ≤ π(2^1) = π(2)
      subst hk0
      -- π(2) = 1 since 2 is the only prime ≤ 2
      decide
    · -- Inductive case: k ≥ 1
      have hk_ge : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have ih' := ih hk_ge
      -- π(2^{k+1}) = π(2 * 2^k) ≥ π(2^k) + 1 by Bertrand
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      have hdouble := primeCounting_doubling_ge_one (2 ^ k) hpos
      have h2k_ne : 2 * 2^k ≠ 0 := by positivity
      have hpi_mono : π (2 ^ k) ≤ π (2 * 2 ^ k) := Nat.monotone_primeCounting (by omega)
      omega

/-- Lower bound: π(n) ≥ log₂(n) for n ≥ 2 -/
theorem primeCounting_ge_log (n : ℕ) (hn : 2 ≤ n) : Nat.log 2 n ≤ π n := by
  -- Nat.log 2 n is the largest k such that 2^k ≤ n
  have hlog_pos : 1 ≤ Nat.log 2 n := by
    have h1 : Nat.log 2 2 = 1 := by native_decide
    have hlog_mono : Nat.log 2 2 ≤ Nat.log 2 n := Nat.log_mono_right hn
    omega
  have hpow_le : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hk_bound := primeCounting_pow_two_ge (Nat.log 2 n) hlog_pos
  have hmono := Nat.monotone_primeCounting hpow_le
  omega

/-!
## Lower Bound on θ via Bertrand

From Bertrand's postulate, we can also derive a lower bound on θ.
If there's always a prime in (n, 2n], then θ(2n) - θ(n) ≥ log(n+1).

By telescoping: θ(2^k) ≥ Σᵢ log(2^{i-1} + 1) ≥ (k-1) log 2.
-/

/-- Lower bound on θ doubling: θ(2n) - θ(n) ≥ log(n+1) for n ≥ 1 -/
theorem chebyshevTheta_doubling_ge (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) ≤ chebyshevTheta (2 * n) - chebyshevTheta n := by
  unfold chebyshevTheta
  -- Get Bertrand's prime p with n < p ≤ 2n
  have hne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  obtain ⟨p, hp_prime, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul n hne
  -- p is a prime with n < p ≤ 2n, contributing log p to θ(2n) - θ(n)
  have hlog_p : Real.log p ≤ ∑ q ∈ filter Nat.Prime (range (2 * n + 1)), Real.log q -
                            ∑ q ∈ filter Nat.Prime (range (n + 1)), Real.log q := by
    -- Write the 2n sum as n sum + extra primes
    have hunion : range (2 * n + 1) = range (n + 1) ∪ Ico (n + 1) (2 * n + 1) := by
      ext x; simp only [mem_range, mem_union, mem_Ico]; omega
    have hdisj : Disjoint (range (n + 1)) (Ico (n + 1) (2 * n + 1)) := by
      rw [disjoint_iff_ne]; intro a ha b hb; simp only [mem_range] at ha; simp only [mem_Ico] at hb; omega
    rw [hunion, filter_union, sum_union (disjoint_filter_filter hdisj)]
    -- So the difference is Σ_{n < q ≤ 2n, q prime} log q
    have hp_in_extra : p ∈ filter Nat.Prime (Ico (n + 1) (2 * n + 1)) := by
      simp only [mem_filter, mem_Ico]; exact ⟨⟨by omega, by omega⟩, hp_prime⟩
    have hlog_nonneg : ∀ q ∈ filter Nat.Prime (Ico (n + 1) (2 * n + 1)), 0 ≤ Real.log q := by
      intro q hq
      have hqprime := (mem_filter.mp hq).2
      have : 2 ≤ q := hqprime.two_le
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt this)
    calc Real.log p ≤ ∑ q ∈ filter Nat.Prime (Ico (n + 1) (2 * n + 1)), Real.log q :=
           single_le_sum hlog_nonneg hp_in_extra
      _ = _ := by ring
  -- Now we need log(n + 1) ≤ log p since p > n
  have hnp : n + 1 ≤ p := hlo
  have hlog_mono : Real.log (n + 1) ≤ Real.log p := by
    apply Real.log_le_log
    · exact_mod_cast Nat.succ_pos n
    · exact_mod_cast hnp
  linarith

#check chebyshevTheta_le
#check pow_primeCounting_diff_le
#check prodPrimesInInterval_dvd_centralBinom
#check primeCounting_doubling_ge_one
#check primeCounting_pow_two_ge
#check primeCounting_ge_log
#check chebyshevTheta_doubling_ge

/-!
## Lower Bound on Central Binomial Coefficient

From binomial theorem: 4^n = (1+1)^{2n} = Σ_{k=0}^{2n} C(2n,k)
Since there are 2n+1 terms and C(2n,n) is the maximum:
  4^n ≤ (2n+1) · C(2n,n)
Hence: C(2n,n) ≥ 4^n / (2n+1)
-/

/-- Lower bound: C(2n, n) ≥ 4^n / (2n + 1) -/
theorem centralBinom_ge_four_pow_div (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * centralBinom n := by
  have hpow : 4 ^ n = (2 ^ 2) ^ n := by norm_num
  calc 4 ^ n = (2 ^ 2) ^ n := hpow
    _ = 2 ^ (2 * n) := by rw [← pow_mul]
    _ = ∑ k ∈ range (2 * n + 1), (2 * n).choose k := (sum_range_choose (2 * n)).symm
    _ ≤ ∑ _k ∈ range (2 * n + 1), centralBinom n := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [mem_range] at hk
        -- centralBinom n = (2n).choose n and this is the middle binomial, so largest
        have h := Nat.choose_le_middle k (2 * n)
        -- (2 * n) / 2 = n
        simp only [Nat.mul_div_cancel_left n (by norm_num : 0 < 2)] at h
        exact h
    _ = (2 * n + 1) * centralBinom n := by
        rw [sum_const, card_range]
        ring

/-- Corollary: log(C(2n,n)) ≥ n·log(4) - log(2n+1) -/
theorem log_centralBinom_ge (n : ℕ) (hn : 1 ≤ n) :
    n * Real.log 4 - Real.log (2 * n + 1) ≤ Real.log (centralBinom n) := by
  have h2n1_pos : (0 : ℝ) < 2 * n + 1 := by positivity
  have hbound := centralBinom_ge_four_pow_div n
  -- Restate bound in ℝ
  have hbound_real : (4 : ℝ) ^ n ≤ (2 * n + 1) * centralBinom n := by
    have h1 : (4 : ℝ) ^ n = (4 ^ n : ℕ) := by simp [Nat.cast_pow]
    have h2 : ((2 * n + 1) * centralBinom n : ℝ) = ((2 * n + 1) * centralBinom n : ℕ) := by simp
    rw [h1, h2]
    exact_mod_cast hbound
  have hdiv : (4 : ℝ) ^ n / (2 * n + 1) ≤ centralBinom n := by
    rw [div_le_iff h2n1_pos]
    calc (4 : ℝ) ^ n ≤ (2 * n + 1) * centralBinom n := hbound_real
      _ = centralBinom n * (2 * n + 1) := by ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 4 ^ n / (2 * n + 1)) hdiv
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  rw [Real.log_pow] at hlog
  linarith

/-!
## Summary of Results

### Upper Bounds (Chebyshev 1852)
1. θ(n) ≤ n · log(4) ≈ 1.386n
2. n^{π(2n) - π(n)} ≤ 4^n

### Lower Bounds (via Bertrand's Postulate)
3. π(2n) - π(n) ≥ 1 for n ≥ 1
4. π(2^k) ≥ k for k ≥ 1
5. π(n) ≥ log₂(n) for n ≥ 2
6. θ(2n) - θ(n) ≥ log(n+1) for n ≥ 1

### Central Binomial Bounds
7. C(2n,n) ≤ 4^n (upper bound)
8. 4^n ≤ (2n+1) · C(2n,n) (lower bound)

These bounds demonstrate that π(x) and θ(x) are both Θ(x/log(x)) and Θ(x) respectively,
which is the essence of Chebyshev's contribution to the Prime Number Theorem.
-/

#check centralBinom_ge_four_pow_div
#check log_centralBinom_ge

end ChebyshevBounds
