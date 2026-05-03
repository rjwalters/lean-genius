/-
# Erdős Problem #1201: Greatest Prime Factor of Consecutive Products

Let P(m) denote the greatest prime divisor of m (with P(1) = 0 by convention).
Let P(n, k) = P(n(n+1)···(n+k)) be the greatest prime factor of k+1 consecutive
integers starting at n.

**Main Conjecture**: For every ε, η > 0 there exists k such that the upper density
of {n : P(n, k) > n^(1-ε)} is at least 1 - η.

**Partial Result** (Erdős): The conjecture holds for ε = 1/2.

*Reference*: [erdosproblems.com/1201](https://erdosproblems.com/1201)
-/

import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Bertrand

namespace Erdos1201

/-
## Greatest Prime Factor
-/

/-- The greatest prime divisor of n. Returns 0 for n = 0 or n = 1 (no prime factors). -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

/-- The product of k+1 consecutive integers starting at n: n(n+1)···(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.range (k + 1)).prod (fun i => n + i)

/-- The greatest prime factor of the consecutive product P(n, k). -/
noncomputable def gpfConsecutive (n k : ℕ) : ℕ :=
  greatestPrimeFactor (consecutiveProduct n k)

/-
## Upper Density
-/

/-- Upper density of a set S ⊆ ℕ: lim sup of |S ∩ [1,N]| / N. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  haveI : DecidablePred (· ∈ S) := Classical.decPred _
  Filter.limsup (fun N : ℕ =>
    (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ))
  Filter.atTop

/-
## Main Conjecture (Open)
-/

/-- **Erdős Problem 1201**: For every ε ∈ (0,1) and η > 0, there exists k such that
    the upper density of {n | P(n,k) > n^(1-ε)} is at least 1 - η. -/
def ErdosProblem1201 : Prop :=
  ∀ (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η),
  ∃ k : ℕ,
    upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η

/-
## Partial Result (Erdős, ε = 1/2)
-/

/-- **Erdős (partial)**: The conjecture holds for ε = 1/2.
    For every η > 0, there exists k such that the upper density of
    {n | P(n,k) > √n} is at least 1 - η. -/
axiom erdos_1201_half_case (η : ℝ) (hη : 0 < η) :
    ∃ k : ℕ,
      upperDensity {n : ℕ | Real.sqrt n < (gpfConsecutive n k : ℝ)} ≥ 1 - η

/-
## Basic Properties of Greatest Prime Factor
-/

/-- For n ≥ 2, greatestPrimeFactor n is prime. -/
theorem gpf_prime (n : ℕ) (hn : 2 ≤ n) : (greatestPrimeFactor n).Prime := by
  unfold greatestPrimeFactor
  have h : n.primeFactors.Nonempty :=
    ⟨n.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩⟩
  rw [dif_pos h]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ h)

/-- greatestPrimeFactor n ∈ n.primeFactors when n ≥ 2. -/
theorem gpf_mem_primeFactors (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∈ n.primeFactors := by
  unfold greatestPrimeFactor
  have h : n.primeFactors.Nonempty :=
    ⟨n.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩⟩
  rw [dif_pos h]
  exact Finset.max'_mem _ h

/-- greatestPrimeFactor n divides n when n ≥ 2. -/
theorem gpf_dvd (n : ℕ) (hn : 2 ≤ n) : greatestPrimeFactor n ∣ n := by
  have h := gpf_mem_primeFactors n hn
  exact (Nat.mem_primeFactors.mp h).2.1

/-- greatestPrimeFactor n ≤ n when n ≥ 2. -/
theorem gpf_le (n : ℕ) (hn : 2 ≤ n) : greatestPrimeFactor n ≤ n :=
  Nat.le_of_dvd (by omega) (gpf_dvd n hn)

/-- greatestPrimeFactor n ≥ 2 when n ≥ 2. -/
theorem gpf_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ greatestPrimeFactor n :=
  (gpf_prime n hn).two_le

/-- Any prime factor of n is ≤ greatestPrimeFactor n. -/
theorem gpf_max (n p : ℕ) (hp : p ∈ n.primeFactors) : p ≤ greatestPrimeFactor n := by
  unfold greatestPrimeFactor
  have h : n.primeFactors.Nonempty := ⟨p, hp⟩
  rw [dif_pos h]
  exact Finset.le_max' _ _ hp

/-- If p is prime and p ∣ n then p ≤ greatestPrimeFactor n. -/
theorem gpf_ge_prime_dvd (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    p ≤ greatestPrimeFactor n :=
  gpf_max n p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)

/-
## Basic Properties of Consecutive Products
-/

/-- consecutiveProduct n 0 = n. -/
theorem consecutiveProduct_zero (n : ℕ) : consecutiveProduct n 0 = n := by
  simp [consecutiveProduct]

/-- consecutiveProduct n 1 = n * (n + 1). -/
theorem consecutiveProduct_one (n : ℕ) : consecutiveProduct n 1 = n * (n + 1) := by
  have := consecutiveProduct_succ n 0
  rwa [consecutiveProduct_zero] at this

/-- consecutiveProduct n k is positive when n ≥ 1. -/
theorem consecutiveProduct_pos (n k : ℕ) (hn : 1 ≤ n) : 0 < consecutiveProduct n k := by
  apply Finset.prod_pos
  intro i _
  omega

/-- n divides consecutiveProduct n k. -/
theorem dvd_consecutiveProduct_left (n k : ℕ) : n ∣ consecutiveProduct n k := by
  simp only [consecutiveProduct]
  have h := Finset.dvd_prod_of_mem (fun i => n + i) (Finset.mem_range.mpr (Nat.succ_pos k))
  simpa using h

/-- (n+k) divides consecutiveProduct n k. -/
theorem dvd_consecutiveProduct_right (n k : ℕ) : n + k ∣ consecutiveProduct n k := by
  simp only [consecutiveProduct]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self k))

/-- consecutiveProduct n k = n * consecutiveProduct (n+1) (k-1) for k ≥ 1. -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = n * consecutiveProduct (n + 1) k := by
  induction k with
  | zero =>
    simp only [consecutiveProduct, Finset.prod_range_succ, Finset.prod_range_zero]
    ring
  | succ k ih =>
    have lh : consecutiveProduct n (k + 2) = consecutiveProduct n (k + 1) * (n + k + 2) := by
      unfold consecutiveProduct
      conv_lhs => rw [Finset.prod_range_succ]
      congr 1
    have rh : consecutiveProduct (n + 1) (k + 1) = consecutiveProduct (n + 1) k * (n + 1 + k + 1) := by
      unfold consecutiveProduct
      conv_lhs => rw [Finset.prod_range_succ]
      congr 1
    show consecutiveProduct n (k + 2) = n * consecutiveProduct (n + 1) (k + 1)
    rw [lh, rh, ih]; ring

/-
## Monotonicity of gpfConsecutive in k
-/

/-- If p divides consecutiveProduct n k, it divides consecutiveProduct n (k+1). -/
theorem dvd_consecutiveProduct_of_dvd_lt (n k : ℕ) (p : ℕ) (hp : p ∣ consecutiveProduct n k) :
    p ∣ consecutiveProduct n (k + 1) := by
  unfold consecutiveProduct at *
  apply Dvd.dvd.trans hp
  apply Finset.prod_dvd_prod_of_subset
  exact Finset.range_mono (Nat.le_succ _)

/-- gpfConsecutive is monotone in k: increasing k can only increase or maintain the gpf. -/
theorem gpfConsecutive_mono (n k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n k ≤ gpfConsecutive n (k + 1) := by
  have hcp1 : 2 ≤ consecutiveProduct n k :=
    Nat.le_trans hn (Nat.le_of_dvd (consecutiveProduct_pos n k (by omega))
      (dvd_consecutiveProduct_left n k))
  have hcp2 : 2 ≤ consecutiveProduct n (k + 1) :=
    Nat.le_trans hn (Nat.le_of_dvd (consecutiveProduct_pos n (k + 1) (by omega))
      (dvd_consecutiveProduct_left n (k + 1)))
  unfold gpfConsecutive
  exact gpf_ge_prime_dvd _ _ hcp2 (gpf_prime _ hcp1)
    (dvd_consecutiveProduct_of_dvd_lt n k _ (gpf_dvd _ hcp1))

/-
## Large Prime Factor Criterion
-/

/-- If there is a prime p ≤ n+k with p ∣ n and p > n^(1-ε), then gpfConsecutive n k > n^(1-ε). -/
theorem gpfConsecutive_large_of_prime_dvd (n k : ℕ) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ n + k) (hpdvd : ∃ i ≤ k, p ∣ n + i)
    (hn : 2 ≤ n) (ε : ℝ) (hpε : (n : ℝ) ^ (1 - ε) < p) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) := by
  obtain ⟨i, hi, hpi⟩ := hpdvd
  -- p ∈ (consecutiveProduct n k).primeFactors
  have h_in_cf : p ∈ (consecutiveProduct n k).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, by
      have := consecutiveProduct_pos n k (by omega); omega⟩
    exact dvd_trans hpi (by
      simp only [consecutiveProduct]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega)))
  have h_le := gpf_max (consecutiveProduct n k) p h_in_cf
  calc (n : ℝ) ^ (1 - ε) < (p : ℝ) := hpε
    _ ≤ (gpfConsecutive n k : ℝ) := by exact_mod_cast h_le

/-
## Asymptotic Growth
-/

/-- consecutiveProduct n k ≥ n when n ≥ 1. -/
theorem consecutiveProduct_ge_n (n k : ℕ) (hn : 1 ≤ n) :
    n ≤ consecutiveProduct n k := by
  calc n = consecutiveProduct n 0 := (consecutiveProduct_zero n).symm
    _ ≤ consecutiveProduct n k := by
        simp only [consecutiveProduct]
        apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono (by omega))
        intro i _ _; omega

/-- gpfConsecutive n k ≥ 2 when n ≥ 2. -/
theorem gpfConsecutive_ge_two (n k : ℕ) (hn : 2 ≤ n) : 2 ≤ gpfConsecutive n k := by
  unfold gpfConsecutive
  apply gpf_ge_two
  calc 2 ≤ n := hn
    _ ≤ consecutiveProduct n k := consecutiveProduct_ge_n n k (by omega)

/-
## Comparison with ε = 1/2 case
-/

/-- The ε = 1/2 condition: P(n, k) > √n is equivalent to P(n,k)² > n, for all n ∈ ℕ. -/
theorem gpfConsecutive_half_iff (n k : ℕ) :
    Real.sqrt n < (gpfConsecutive n k : ℝ) ↔
    n < (gpfConsecutive n k) ^ 2 := by
  constructor
  · intro h
    have h1 : (n : ℝ) < (gpfConsecutive n k : ℝ) ^ 2 :=
      calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
        _ < _ := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
    exact_mod_cast h1
  · intro h
    by_cases hgpf : gpfConsecutive n k = 0
    · simp [hgpf] at h
    · have hgpf_pos : 0 < (gpfConsecutive n k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hgpf)
      have h1 : (n : ℝ) < (gpfConsecutive n k : ℝ) ^ 2 := by exact_mod_cast h
      calc Real.sqrt n < Real.sqrt ((gpfConsecutive n k : ℝ) ^ 2) :=
            Real.sqrt_lt_sqrt (Nat.cast_nonneg n) h1
        _ = gpfConsecutive n k := Real.sqrt_sq hgpf_pos.le

/-- The ε = 1/2 partial result specializes to: ∀ η > 0, ∃ k, density of
    {n | gpfConsecutive n k² > n} ≥ 1 - η. -/
theorem erdos_1201_half_squared (η : ℝ) (hη : 0 < η) :
    ∃ k : ℕ,
      upperDensity {n : ℕ | n < (gpfConsecutive n k) ^ 2} ≥ 1 - η := by
  obtain ⟨k, hk⟩ := erdos_1201_half_case η hη
  refine ⟨k, ?_⟩
  have heq : {n : ℕ | Real.sqrt ↑n < ↑(gpfConsecutive n k)} =
             {n : ℕ | n < (gpfConsecutive n k) ^ 2} :=
    Set.ext (fun n => gpfConsecutive_half_iff n k)
  rw [← heq]; exact hk

/-
## Bertrand's Postulate Consequences
-/

/-- By Bertrand's postulate, gpfConsecutive n n > n for n ≥ 1.
    The window [n, 2n] always contains a prime exceeding n. -/
theorem gpfConsecutive_self_gt (n : ℕ) (hn : 1 ≤ n) :
    n < gpfConsecutive n n := by
  obtain ⟨p, hp_prime, hn_lt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  -- p ∈ (n, 2n], so p = n + (p - n) with 1 ≤ p - n ≤ n
  have h_dvd : p ∣ consecutiveProduct n n := by
    unfold consecutiveProduct
    have heq : p = n + (p - n) := by omega
    rw [heq]
    exact Finset.dvd_prod_of_mem (fun i => n + i) (Finset.mem_range.mpr (by omega))
  have h_pos : 0 < consecutiveProduct n n := consecutiveProduct_pos n n hn
  have h_in : p ∈ (consecutiveProduct n n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, h_dvd, h_pos.ne'⟩
  exact Nat.lt_of_lt_of_le hn_lt (gpf_max (consecutiveProduct n n) p h_in)

/-- For n ≥ 2 and k ≥ n, gpfConsecutive n k > n:
    any window of length ≥ n starting at n ≥ 2 contains a prime > n. -/
theorem gpfConsecutive_gt_n_of_large_window (n k : ℕ) (hn : 2 ≤ n) (hk : n ≤ k) :
    n < gpfConsecutive n k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact gpfConsecutive_self_gt n (by omega)
  | succ d ih =>
    exact Nat.lt_of_lt_of_le (ih (by omega)) (gpfConsecutive_mono n (n + d) hn)

/-
## Prime Start Lower Bound
-/

/-- For prime n and any window width k, gpfConsecutive n k ≥ n.
    Since n is prime and n divides the consecutive product (as its first term),
    n is a prime factor of the product, so the greatest prime factor is ≥ n. -/
theorem gpfConsecutive_ge_self_of_prime (n k : ℕ) (hn : n.Prime) :
    n ≤ gpfConsecutive n k := by
  have h_cp_ge_n := consecutiveProduct_ge_n n k (by linarith [hn.two_le])
  exact gpf_ge_prime_dvd (consecutiveProduct n k) n
    (le_trans hn.two_le h_cp_ge_n) hn (dvd_consecutiveProduct_left n k)

/-
## Term Divisibility
-/

/-- Each term (n+i) for i ≤ k divides consecutiveProduct n k.
    Generalizes dvd_consecutiveProduct_right (the i=k case). -/
theorem dvd_consecutiveProduct_term (n k i : ℕ) (hi : i ≤ k) :
    n + i ∣ consecutiveProduct n k := by
  simp only [consecutiveProduct]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))

/-
## Sylvester-Schur: Prime Factor Exceeds Window Size
-/

/-- If a prime p lies inside the window [n, n+k] and n > k,
    then gpfConsecutive n k > k (since p ≥ n > k is a prime factor of the product). -/
theorem gpfConsecutive_gt_k_of_prime_in_window (n k : ℕ) (hkn : k < n)
    (p : ℕ) (hp_prime : p.Prime) (hn_le : n ≤ p) (hp_le : p ≤ n + k) :
    k < gpfConsecutive n k := by
  have h_pos : 0 < consecutiveProduct n k := consecutiveProduct_pos n k (by omega)
  have h_dvd : p ∣ consecutiveProduct n k := by
    have h_offset : p - n ≤ k := by omega
    have heq : n + (p - n) = p := by omega
    exact heq ▸ dvd_consecutiveProduct_term n k (p - n) h_offset
  have h_in : p ∈ (consecutiveProduct n k).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, h_dvd, h_pos.ne'⟩
  exact Nat.lt_of_lt_of_le (by omega) (gpf_max _ p h_in)

/-- **Sylvester-Schur (base case)**: For k ≥ 1, gpfConsecutive (k+1) k > k.
    The Bertrand prime p ∈ (k, 2k] lies inside [k+1, 2k+1] = [n, n+k], giving a
    prime factor p > k of the consecutive product n(n+1)···(2k+1). -/
theorem gpfConsecutive_succ_gt_k (k : ℕ) (hk : 1 ≤ k) :
    k < gpfConsecutive (k + 1) k := by
  obtain ⟨p, hp_prime, hk_lt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
  exact gpfConsecutive_gt_k_of_prime_in_window (k + 1) k (by omega) p hp_prime
    (by omega) (by omega)

/-- **Sylvester-Schur (diagonal)**: For n ≥ 2, gpfConsecutive n (n-1) > n-1.
    The product n(n+1)···(2n-1) always has a prime factor exceeding n-1. -/
theorem gpfConsecutive_gt_pred_self (n : ℕ) (hn : 2 ≤ n) :
    n - 1 < gpfConsecutive n (n - 1) := by
  have h := gpfConsecutive_succ_gt_k (n - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h

/-
## Infinitely Many n with Large GPF
-/

/-- For any fixed k and ε ∈ (0,1), infinitely many n satisfy P(n,k) > n^(1-ε).
    Every prime n satisfies P(n,k) ≥ n > n^(1-ε), so the set of good n contains all primes. -/
theorem erdos_1201_infinitely_many (k : ℕ) (ε : ℝ) (hε₀ : 0 < ε) (_hε₁ : ε < 1) :
    Set.Infinite {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} := by
  apply Nat.infinite_setOf_prime.mono
  intro n hn
  simp only [Set.mem_setOf_eq] at *
  have h_ge : n ≤ gpfConsecutive n k := gpfConsecutive_ge_self_of_prime n k hn
  have h_real : (n : ℝ) ≤ (gpfConsecutive n k : ℝ) := by exact_mod_cast h_ge
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast hn.one_lt
  calc (n : ℝ) ^ (1 - ε)
      < (n : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith)
    _ = (n : ℝ) := Real.rpow_one _
    _ ≤ (gpfConsecutive n k : ℝ) := h_real

/-
## Upper Bounds and Tight Estimates
-/

/-- gpfConsecutive n 0 = greatestPrimeFactor n: window of width 0 is just the starting term. -/
theorem gpfConsecutive_zero (n : ℕ) : gpfConsecutive n 0 = greatestPrimeFactor n := by
  simp [gpfConsecutive, consecutiveProduct_zero]

/-- If p is prime and divides ∏ i < k+1, (n+i), then p divides some n+i with i < k+1. -/
private lemma prime_dvd_consecutive_range (n k : ℕ) (p : ℕ) (hp : p.Prime)
    (h : p ∣ (Finset.range (k + 1)).prod (fun i => n + i)) :
    ∃ i < k + 1, p ∣ n + i := by
  induction k with
  | zero => exact ⟨0, Nat.lt_succ_self 0, by simpa using h⟩
  | succ k ih =>
    rw [Finset.prod_range_succ] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · obtain ⟨i, hi, hpi⟩ := ih h1
      exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self _), hpi⟩
    · exact ⟨k + 1, Nat.lt_succ_self _, h2⟩

/-- Upper bound: every prime factor of the window [n, n+k] is ≤ n+k, so P(n,k) ≤ n+k. -/
theorem gpfConsecutive_upper_bound (n k : ℕ) (hn : 1 ≤ n) :
    gpfConsecutive n k ≤ n + k := by
  unfold gpfConsecutive greatestPrimeFactor
  split_ifs with h
  swap; · exact Nat.zero_le _
  apply Finset.max'_le _ h
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hp_prime, hp_dvd, _⟩ := hp
  have hdvd : ∃ i < k + 1, p ∣ n + i :=
    prime_dvd_consecutive_range n k p hp_prime hp_dvd
  obtain ⟨i, hi, hpi⟩ := hdvd
  exact Nat.le_trans (Nat.le_of_dvd (by omega) hpi) (by omega)

/-- Lower bound: if prime p divides term n+i in the window (i ≤ k), then p ≤ P(n,k). -/
theorem le_gpfConsecutive_of_prime_dvd_term (n k i : ℕ) (hn : 1 ≤ n) (hi : i ≤ k) (p : ℕ)
    (hp : p.Prime) (hpdvd : p ∣ n + i) : p ≤ gpfConsecutive n k := by
  have hcp : 2 ≤ consecutiveProduct n k :=
    Nat.le_trans hp.two_le
      (Nat.le_trans (Nat.le_of_dvd (by omega) hpdvd)
        (Nat.le_of_dvd (consecutiveProduct_pos n k hn)
          (dvd_consecutiveProduct_term n k i hi)))
  unfold gpfConsecutive
  exact gpf_ge_prime_dvd (consecutiveProduct n k) p hcp hp
    (dvd_trans hpdvd (dvd_consecutiveProduct_term n k i hi))

/-- Tight Bertrand bound: for n ≥ 1, n < P(n,n) ≤ 2n (prime in Bertrand window). -/
theorem gpfConsecutive_between (n : ℕ) (hn : 1 ≤ n) :
    n < gpfConsecutive n n ∧ gpfConsecutive n n ≤ 2 * n := by
  exact ⟨gpfConsecutive_self_gt n hn,
         by have := gpfConsecutive_upper_bound n n hn; omega⟩

/-
## Upper Bounds and Bertrand Structure
-/

/-- The GPF of k+1 consecutive integers starting at n is at most n+k: every prime dividing
    the product divides some factor n+i ≤ n+k. -/
theorem gpfConsecutive_le_right (n k : ℕ) (hn : 1 ≤ n) :
    gpfConsecutive n k ≤ n + k := by
  unfold gpfConsecutive greatestPrimeFactor
  by_cases h : (consecutiveProduct n k).primeFactors.Nonempty
  · rw [dif_pos h]
    apply Finset.max'_le _ h
    intro p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    obtain ⟨hp_prime, hp_dvd, _⟩ := hp_mem
    obtain ⟨i, hi_lt, hi_dvd⟩ := prime_dvd_consecutive_range n k p hp_prime hp_dvd
    have hp_le_ni : p ≤ n + i := Nat.le_of_dvd (by omega) hi_dvd
    omega
  · rw [dif_neg h]; omega

/-- When n+k is prime, gpfConsecutive n k = n+k: the prime right endpoint is the largest
    prime factor, since it divides the product and all prime factors are ≤ n+k. -/
theorem gpfConsecutive_eq_of_prime_right (n k : ℕ) (hn : 1 ≤ n) (hprime : (n + k).Prime) :
    gpfConsecutive n k = n + k := by
  apply Nat.le_antisymm
  · exact gpfConsecutive_le_right n k hn
  · have hmem : n + k ∈ (consecutiveProduct n k).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hprime, dvd_consecutiveProduct_right n k,
             by have := consecutiveProduct_pos n k hn; omega⟩
    exact gpf_max (consecutiveProduct n k) (n + k) hmem

/-- Bertrand's postulate implies that for every n ≥ 1, there exists k ≤ n with n+k prime
    and gpfConsecutive n k = n+k. This gives a concrete lower bound: for any n, a window
    of at most n+1 consecutive integers achieves GPF equal to the right endpoint. -/
theorem gpfConsecutive_bertrand (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, k ≤ n ∧ (n + k).Prime ∧ gpfConsecutive n k = n + k := by
  obtain ⟨p, hp_prime, hn_lt_p, hp_le_2n⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hsum : n + (p - n) = p := by omega
  refine ⟨p - n, by omega, ?_, ?_⟩
  · rwa [hsum]
  · exact gpfConsecutive_eq_of_prime_right n (p - n) hn (by rwa [hsum])

/-
## Max Formula and Smooth-Number Reformulation
-/

/-- **Max Formula**: P(n,k) equals the supremum of individual term GPFs.
    The prime factors of n(n+1)···(n+k) are exactly the union of prime factors
    of each term, so the greatest prime factor of the product equals the maximum
    greatest prime factor of the individual terms.

    Consequence: P(n,k) > T iff some term n+i (i ≤ k) has a prime factor > T.
    This connects the Erdős conjecture to the density of windows where all k+1
    consecutive integers are T-smooth (have no prime factor > T). -/
theorem gpfConsecutive_eq_sup_range (n k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n k = (Finset.range (k + 1)).sup (fun i => greatestPrimeFactor (n + i)) := by
  have hprod_ge : 2 ≤ consecutiveProduct n k :=
    le_trans hn (consecutiveProduct_ge_n n k (by omega))
  apply Nat.le_antisymm
  · -- gpfConsecutive n k ≤ sup: the product's GPF divides some term n+i, so ≤ GPF(n+i) ≤ sup
    obtain ⟨i, hi_lt, hi_dvd⟩ :=
      prime_dvd_consecutive_range n k _ (gpf_prime _ hprod_ge) (gpf_dvd _ hprod_ge)
    exact le_trans (gpf_ge_prime_dvd _ _ (by omega) (gpf_prime _ hprod_ge) hi_dvd)
                   (Finset.le_sup (f := fun i => greatestPrimeFactor (n + i))
                     (Finset.mem_range.mpr hi_lt))
  · -- sup ≤ gpfConsecutive n k: for each i, GPF(n+i) | n+i | product, so ≤ GPF(product)
    apply Finset.sup_le
    intro i hi
    rw [Finset.mem_range] at hi
    exact gpf_ge_prime_dvd _ _ hprod_ge (gpf_prime _ (by omega))
      (Nat.dvd_trans (gpf_dvd _ (by omega)) (dvd_consecutiveProduct_term n k i (by omega)))

/-- **Smooth-Window Reformulation**: P(n,k) ≤ t iff all k+1 consecutive integers n+i (i ≤ k)
    have greatest prime factor ≤ t (i.e., are t-smooth).

    This reformulates "n is a bad case for the Erdős conjecture" as "all consecutive integers
    in the window [n, n+k] are t-smooth." The density of such smooth windows → 0 as k → ∞
    (by smooth number theory), which is the key to proving the conjecture. -/
theorem gpfConsecutive_le_iff (n k : ℕ) (hn : 2 ≤ n) (t : ℕ) :
    gpfConsecutive n k ≤ t ↔ ∀ i ≤ k, greatestPrimeFactor (n + i) ≤ t := by
  rw [gpfConsecutive_eq_sup_range n k hn, Finset.sup_le_iff]
  constructor
  · intro h i hi; exact h i (Finset.mem_range.mpr (by omega))
  · intro h i hi; rw [Finset.mem_range] at hi; exact h i (by omega)

/-
## Greatest Prime Factor for Primes and Short Windows
-/

/-- For a prime n, greatestPrimeFactor n = n:
    the prime factorization of a prime is {n}, so its maximum is n itself. -/
theorem greatestPrimeFactor_prime (n : ℕ) (hn : n.Prime) : greatestPrimeFactor n = n :=
  Nat.le_antisymm (gpf_le n hn.two_le) (gpf_ge_prime_dvd n n hn.two_le hn dvd_rfl)

/-- For a prime n, gpfConsecutive n 0 = n: the zero-width window contains only n. -/
theorem gpfConsecutive_prime_start (n : ℕ) (hn : n.Prime) : gpfConsecutive n 0 = n := by
  rw [gpfConsecutive_zero, greatestPrimeFactor_prime n hn]

/-- P(n, 1) = max(gpf(n), gpf(n+1)): the length-2 window's GPF is the maximum
    of the individual greatest prime factors. Since prime factor sets of n and n+1
    are disjoint (consecutive integers are coprime), the product's GPF comes from one term. -/
theorem gpfConsecutive_one_eq_max (n : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n 1 = max (greatestPrimeFactor n) (greatestPrimeFactor (n + 1)) := by
  rw [gpfConsecutive_eq_sup_range n 1 hn]
  simp only [show 1 + 1 = 2 from rfl, show (Finset.range 2 : Finset ℕ) = {0, 1} from by decide,
             Finset.sup_insert, Finset.sup_singleton]
  simp only [Nat.add_zero]

/-- For n ≥ 2, the greatest prime factors of n and n+1 are coprime.
    Since gcd(n, n+1) = 1 and gpf(n) ∣ n, gpf(n+1) ∣ n+1, the gcd of the gpfs divides 1. -/
theorem gpfConsecutive_one_coprime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Coprime (greatestPrimeFactor n) (greatestPrimeFactor (n + 1)) := by
  have hdn : greatestPrimeFactor n ∣ n := gpf_dvd n hn
  have hdn1 : greatestPrimeFactor (n + 1) ∣ n + 1 := gpf_dvd (n + 1) (by omega)
  have hcop : Nat.Coprime n (n + 1) := Nat.coprime_succ_self n
  have h1 : Nat.gcd (greatestPrimeFactor n) (greatestPrimeFactor (n + 1)) ∣ n :=
    dvd_trans (Nat.gcd_dvd_left _ _) hdn
  have h2 : Nat.gcd (greatestPrimeFactor n) (greatestPrimeFactor (n + 1)) ∣ n + 1 :=
    dvd_trans (Nat.gcd_dvd_right _ _) hdn1
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)

/-- For n ≥ 2, greatestPrimeFactor n ≠ greatestPrimeFactor (n + 1).
    If equal to p ≥ 2, then gcd(p, p) = p ≥ 2 contradicts the coprimality above. -/
theorem gpfConsecutive_one_ne (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ≠ greatestPrimeFactor (n + 1) := by
  intro h
  have hcop := gpfConsecutive_one_coprime n hn
  have hge : 2 ≤ greatestPrimeFactor n := gpf_ge_two n hn
  have heq : Nat.gcd (greatestPrimeFactor n) (greatestPrimeFactor n) = 1 := h ▸ hcop
  rw [Nat.gcd_self] at heq
  omega

/-- P(n, k) ≥ gpf(n): the window GPF is at least the GPF of the left endpoint. -/
theorem gpfConsecutive_ge_left (n k : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ≤ gpfConsecutive n k := by
  rw [gpfConsecutive_eq_sup_range n k hn]
  have h := Finset.le_sup (f := fun i => greatestPrimeFactor (n + i))
              (Finset.mem_range.mpr (Nat.succ_pos k))
  simpa using h

/-- P(n, k) ≥ gpf(n+k): the window GPF is at least the GPF of the right endpoint. -/
theorem gpfConsecutive_ge_right (n k : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor (n + k) ≤ gpfConsecutive n k := by
  rw [gpfConsecutive_eq_sup_range n k hn]
  exact Finset.le_sup (f := fun i => greatestPrimeFactor (n + i))
    (Finset.mem_range.mpr (Nat.lt_succ_self k))


/-
## GPF of Products
-/

/-- The greatest prime factor of a product a*b equals the maximum of the individual
    greatest prime factors: gpf(a*b) = max(gpf(a), gpf(b)) for a, b ≥ 2.

    Key: any prime p dividing a*b must divide a or b (by primality), giving the ≤ direction.
    The ≥ direction follows because gpf(a) | a | a*b, so gpf(a) ≤ gpf(a*b). -/
theorem greatestPrimeFactor_mul (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    greatestPrimeFactor (a * b) = max (greatestPrimeFactor a) (greatestPrimeFactor b) := by
  have hab : 2 ≤ a * b := by nlinarith
  apply Nat.le_antisymm
  · have hp := gpf_prime _ hab
    rcases hp.dvd_mul.mp (gpf_dvd _ hab) with h | h
    · exact le_trans (gpf_max a _ (Nat.mem_primeFactors.mpr ⟨hp, h, by omega⟩)) (le_max_left _ _)
    · exact le_trans (gpf_max b _ (Nat.mem_primeFactors.mpr ⟨hp, h, by omega⟩)) (le_max_right _ _)
  · apply max_le
    · exact gpf_ge_prime_dvd _ _ hab (gpf_prime a ha) (dvd_trans (gpf_dvd a ha) (dvd_mul_right a b))
    · exact gpf_ge_prime_dvd _ _ hab (gpf_prime b hb) (dvd_trans (gpf_dvd b hb) (dvd_mul_left b a))

/-
## General Monotonicity and Recursive Formula
-/

/-- **General k-monotonicity**: gpfConsecutive n k₁ ≤ gpfConsecutive n k₂ for k₁ ≤ k₂.
    Extends the one-step `gpfConsecutive_mono` to arbitrary window extensions.
    Proof: the sup over range(k₁+1) ≤ sup over range(k₂+1) by subset monotonicity. -/
theorem gpfConsecutive_le_of_le_k (n : ℕ) (hn : 2 ≤ n) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    gpfConsecutive n k₁ ≤ gpfConsecutive n k₂ := by
  rw [gpfConsecutive_eq_sup_range n k₁ hn, gpfConsecutive_eq_sup_range n k₂ hn]
  apply Finset.sup_le
  intro i hi
  apply Finset.le_sup
  rw [Finset.mem_range] at hi ⊢
  omega

/-- **One-Step Recursive Formula**: P(n, k+1) = max(P(n, k), gpf(n+k+1)) for n ≥ 2.
    Extending the window by one term on the right adds at most one new maximal prime factor.
    This gives a clean recursion: the window GPF grows by absorbing the right endpoint's GPF. -/
theorem gpfConsecutive_succ_right (n k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n (k + 1) = max (gpfConsecutive n k) (greatestPrimeFactor (n + k + 1)) := by
  rw [gpfConsecutive_eq_sup_range n (k + 1) hn, gpfConsecutive_eq_sup_range n k hn,
      show k + 1 + 1 = (k + 1) + 1 from rfl, Finset.range_succ, Finset.sup_insert]
  simp only [show n + (k + 1) = n + k + 1 from by ring]
  rw [sup_comm]

/-
## Right-Endpoint Biconditional and Infinite Sets
-/

/-- **Right-Endpoint Biconditional**: P(n,k) = n+k ↔ (n+k).Prime.
    The upper bound gpfConsecutive_upper_bound (P ≤ n+k) is achieved exactly when the right
    endpoint n+k is prime. -/
theorem gpfConsecutive_eq_right_iff (n k : ℕ) (hn : 1 ≤ n) (hnk : 2 ≤ n + k) :
    gpfConsecutive n k = n + k ↔ (n + k).Prime := by
  constructor
  · intro h
    have hcp_ge : 2 ≤ consecutiveProduct n k :=
      le_trans hnk (Nat.le_of_dvd (consecutiveProduct_pos n k hn)
        (dvd_consecutiveProduct_right n k))
    have hprime : (gpfConsecutive n k).Prime := by
      unfold gpfConsecutive; exact gpf_prime _ hcp_ge
    rwa [h] at hprime
  · exact gpfConsecutive_eq_of_prime_right n k hn

/-- For any fixed k, the set {n | n+k is prime} is infinite. -/
theorem erdos_1201_prime_right_infinite (k : ℕ) :
    Set.Infinite {n : ℕ | (n + k).Prime} := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + k + 1)
  refine ⟨p - k, ?_, by omega⟩
  simp only [Set.mem_setOf_eq]
  rwa [Nat.sub_add_cancel (by omega)]

/-- For any k ≥ 1, infinitely many n satisfy P(n,k) = n+k: the upper bound is achieved
    infinitely often. -/
theorem erdos_1201_eq_right_infinite (k : ℕ) (hk : 0 < k) :
    Set.Infinite {n : ℕ | gpfConsecutive n k = n + k} := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max N 1 + k + 1)
  refine ⟨p - k, ?_, by omega⟩
  simp only [Set.mem_setOf_eq]
  exact gpfConsecutive_eq_of_prime_right (p - k) k (by omega)
    (by rwa [Nat.sub_add_cancel (by omega)])

/-
## Window Extension and Concatenation Formulas
-/

/-- Left-endpoint extension: P(n, k+1) = max(gpf(n), P(n+1, k)) for n ≥ 2.
    Symmetric to gpfConsecutive_succ_right; the window [n, n+k+1] can be viewed as
    prepending n to the tail window [n+1, n+k+1]. -/
theorem gpfConsecutive_succ_left (n k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n (k + 1) = max (greatestPrimeFactor n) (gpfConsecutive (n + 1) k) := by
  have hn1 : 2 ≤ n + 1 := by omega
  apply Nat.le_antisymm
  · rw [gpfConsecutive_eq_sup_range n (k + 1) hn]
    apply Finset.sup_le
    intro i hi
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [Nat.add_zero]; exact le_max_left _ _
    · have heq : greatestPrimeFactor (n + i) = greatestPrimeFactor (n + 1 + (i - 1)) := by
        congr 1; omega
      rw [heq]
      exact le_trans
        (by rw [gpfConsecutive_eq_sup_range (n + 1) k hn1]
            exact Finset.le_sup (f := fun j => greatestPrimeFactor (n + 1 + j))
              (Finset.mem_range.mpr (by omega)))
        (le_max_right _ _)
  · apply max_le
    · exact gpfConsecutive_ge_left n (k + 1) hn
    · rw [gpfConsecutive_eq_sup_range (n + 1) k hn1, gpfConsecutive_eq_sup_range n (k + 1) hn]
      apply Finset.sup_le
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show n + 1 + i = n + (i + 1) from by omega]
      exact Finset.le_sup (f := fun j => greatestPrimeFactor (n + j))
        (Finset.mem_range.mpr (by omega))

/-- Window concatenation: P(n, j+k+1) = max(P(n,j), P(n+j+1,k)) for n ≥ 2.
    The window [n, n+j+k+1] splits into halves [n, n+j] and [n+j+1, n+j+k+1].
    The greatest prime factor of the full window is the max of both halves. -/
theorem gpfConsecutive_window_concat (n j k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n (j + k + 1) = max (gpfConsecutive n j) (gpfConsecutive (n + j + 1) k) := by
  have hn' : 2 ≤ n + j + 1 := by omega
  apply Nat.le_antisymm
  · rw [gpfConsecutive_eq_sup_range n (j + k + 1) hn]
    apply Finset.sup_le
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h : i ≤ j
    · exact le_trans
        (by rw [gpfConsecutive_eq_sup_range n j hn]
            exact Finset.le_sup (f := fun m => greatestPrimeFactor (n + m))
              (Finset.mem_range.mpr (by omega)))
        (le_max_left _ _)
    · push_neg at h
      have heq : greatestPrimeFactor (n + i) = greatestPrimeFactor (n + j + 1 + (i - j - 1)) := by
        congr 1; omega
      rw [heq]
      exact le_trans
        (by rw [gpfConsecutive_eq_sup_range (n + j + 1) k hn']
            exact Finset.le_sup (f := fun m => greatestPrimeFactor (n + j + 1 + m))
              (Finset.mem_range.mpr (by omega)))
        (le_max_right _ _)
  · apply max_le
    · rw [gpfConsecutive_eq_sup_range n j hn, gpfConsecutive_eq_sup_range n (j + k + 1) hn]
      apply Finset.sup_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact Finset.le_sup (f := fun m => greatestPrimeFactor (n + m))
        (Finset.mem_range.mpr (by omega))
    · rw [gpfConsecutive_eq_sup_range (n + j + 1) k hn', gpfConsecutive_eq_sup_range n (j + k + 1) hn]
      apply Finset.sup_le
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show n + j + 1 + i = n + (j + 1 + i) from by omega]
      exact Finset.le_sup (f := fun m => greatestPrimeFactor (n + m))
        (Finset.mem_range.mpr (by omega))

/-- A prime term in the window gives a lower bound on the window GPF.
    If n+i is prime (i ≤ k), then gpfConsecutive n k ≥ n+i. -/
theorem gpfConsecutive_ge_prime_term (n k i : ℕ) (hn : 2 ≤ n) (hi : i ≤ k)
    (hprime : (n + i).Prime) : n + i ≤ gpfConsecutive n k := by
  rw [← greatestPrimeFactor_prime _ hprime, gpfConsecutive_eq_sup_range n k hn]
  exact Finset.le_sup (f := fun j => greatestPrimeFactor (n + j))
    (Finset.mem_range.mpr (by omega))

/-- Sufficient condition for n to be good for the Erdős problem:
    if the window [n, n+k] contains a prime p > n^(1-ε), then P(n,k) > n^(1-ε).
    This is the structural link between prime distribution and the density result. -/
theorem erdos_1201_good_of_prime_in_window (n k i : ℕ) (ε : ℝ) (hn : 2 ≤ n) (hi : i ≤ k)
    (hprime : (n + i).Prime) (hlarge : (n : ℝ) ^ (1 - ε) < n + i) :
    (n : ℝ) ^ (1 - ε) < gpfConsecutive n k :=
  hlarge.trans_le (by exact_mod_cast gpfConsecutive_ge_prime_term n k i hn hi hprime)

/-- **GPF Localization**: When gpfConsecutive n k > k, the GPF comes from a single term.
    Since p = P(n,k) > k divides the product, it divides some term n+j (j ≤ k).
    As p > k ≥ any difference of indices, p divides at most one term, so p = gpf(n+j). -/
theorem gpfConsecutive_eq_term_gpf (n k : ℕ) (hn : 2 ≤ n) (hk : k < gpfConsecutive n k) :
    ∃ j ≤ k, gpfConsecutive n k = greatestPrimeFactor (n + j) := by
  have hcp : 2 ≤ consecutiveProduct n k :=
    le_trans hn (consecutiveProduct_ge_n n k (by omega))
  have hp : (gpfConsecutive n k).Prime := gpf_prime _ hcp
  have hdvd : gpfConsecutive n k ∣ consecutiveProduct n k := gpf_dvd _ hcp
  obtain ⟨j, hj_lt, hpj⟩ := prime_dvd_consecutive_range n k _ hp hdvd
  have hnj : 2 ≤ n + j := by omega
  exact ⟨j, by omega, Nat.le_antisymm
    (gpf_ge_prime_dvd (n + j) _ hnj hp hpj)
    (gpf_ge_prime_dvd _ (greatestPrimeFactor (n + j)) hcp (gpf_prime _ hnj)
      (dvd_trans (gpf_dvd _ hnj) (dvd_consecutiveProduct_term n k j (by omega))))⟩

end Erdos1201
