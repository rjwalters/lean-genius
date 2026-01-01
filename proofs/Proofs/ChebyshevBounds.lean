/-
# Chebyshev's Prime Counting Bounds

This file proves explicit bounds on the prime counting function using
Chebyshev's 1852 method via central binomial coefficients and primorials.

**Status**: IN PROGRESS
- Proves upper bound on θ(n) via primorial
- Proves upper bound on π(2n) - π(n) using central binomial
- Connects to Chebyshev's functions θ(x)

**Key Results**:
- θ(n) ≤ n · log 4 (weak Chebyshev upper bound)
- n^{π(2n) - π(n)} ≤ 4^n for n ≥ 1
- The product of primes in (n, 2n] divides C(2n, n)

**Historical Context**:
Chebyshev (1852) proved that π(x) is asymptotic to x/log(x) up to constants,
well before the Prime Number Theorem was proved in 1896.

**Mathlib Dependencies**:
- `Nat.primorial` and `primorial_le_4_pow`
- `Nat.centralBinom` and factorization theorems
- `Nat.primeCounting` (π function)
- `Real.log` for logarithmic bounds
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
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

#check chebyshevTheta_le
#check pow_primeCounting_diff_le
#check prodPrimesInInterval_dvd_centralBinom

end ChebyshevBounds
