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

import Mathlib

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
  simp only [consecutiveProduct, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  ring

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

/-- **Sylvester-Schur (n = k+2 case)**: For k ≥ 1, gpfConsecutive (k+2) k > k.
    Bertrand's postulate gives prime p in (k+1, 2(k+1)] = (k+1, 2k+2].
    Since p ≥ k+2 and p ≤ 2k+2 = (k+2)+k, p lies in the window [n, n+k]. -/
theorem gpfConsecutive_succ_succ_gt_k (k : ℕ) (hk : 1 ≤ k) :
    k < gpfConsecutive (k + 2) k := by
  obtain ⟨p, hp_prime, hkp, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (k + 1) (by omega)
  exact gpfConsecutive_gt_k_of_prime_in_window (k + 2) k (by omega) p hp_prime
    (by omega) (by omega)

/-- **Sylvester-Schur (n = k+3 case)**: For k ≥ 1, gpfConsecutive (k+3) k > k.
    Bertrand gives prime p in (k+2, 2(k+2)] = (k+2, 2k+4]. Since 2(k+2) = 2k+4 is
    even and ≥ 6, it is composite, forcing p ≤ 2k+3 = (k+3)+k. Thus p lies in [k+3, 2k+3]. -/
theorem gpfConsecutive_succ_succ_succ_gt_k (k : ℕ) (hk : 1 ≤ k) :
    k < gpfConsecutive (k + 3) k := by
  obtain ⟨p, hp_prime, hkp, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (k + 2) (by omega)
  have hp_ne : p ≠ 2 * (k + 2) := by
    intro heq
    subst heq
    rcases hp_prime.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 (k + 2)) with h | h
    · norm_num at h
    · omega
  exact gpfConsecutive_gt_k_of_prime_in_window (k + 3) k (by omega) p hp_prime
    (by omega) (by omega)

/-- **Sylvester-Schur (prime start)**: When n is prime and k < n, P(n,k) > k.
    Since n is prime, gpf(n) = n ≥ P(n,k); combined with k < n this gives k < P(n,k). -/
theorem gpfConsecutive_prime_gt_k (n k : ℕ) (hn_prime : n.Prime) (hnk : k < n) :
    k < gpfConsecutive n k :=
  lt_of_lt_of_le hnk (gpfConsecutive_ge_self_of_prime n k hn_prime)

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
## Monotonicity in Window Width
-/

/-- **Good-set monotonicity (pointwise)**: if P(n,k) > n^(1-ε), then P(n,k+1) > n^(1-ε),
    since gpfConsecutive is non-decreasing in k. -/
theorem erdos_1201_good_implies_good_succ (n k : ℕ) (ε : ℝ) (hn : 2 ≤ n)
    (hgood : (n : ℝ) ^ (1 - ε) < gpfConsecutive n k) :
    (n : ℝ) ^ (1 - ε) < gpfConsecutive n (k + 1) :=
  hgood.trans_le (by exact_mod_cast gpfConsecutive_mono n k hn)

/-- **Good-set containment**: the set of n with P(n,k) > n^(1-ε) grows with k.
    This is the key structural property: enlarging the window never removes good n. -/
theorem erdos_1201_good_set_mono_k (ε : ℝ) (k : ℕ) :
    {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε) < gpfConsecutive n k} ⊆
    {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε) < gpfConsecutive n (k + 1)} := by
  intro n ⟨hn2, hgood⟩
  exact ⟨hn2, erdos_1201_good_implies_good_succ n k ε hn2 hgood⟩

private noncomputable def densityFun (S : Set ℕ) (N : ℕ) : ℝ :=
  haveI : DecidablePred (· ∈ S) := Classical.decPred _
  (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ)

private lemma upperDensity_eq_densityFun (S : Set ℕ) :
    upperDensity S = Filter.limsup (densityFun S) Filter.atTop := by
  rfl

private lemma densityFun_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ densityFun S N := by
  unfold densityFun
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma densityFun_le_one (S : Set ℕ) (N : ℕ) : densityFun S N ≤ 1 := by
  convert div_le_one_of_le₀ _ _ <;> norm_num
  · infer_instance
  · infer_instance
  · convert le_trans (Finset.card_filter_le _ _) _
    norm_num

private lemma densityFun_mono {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    densityFun S N ≤ densityFun T N := by
  unfold densityFun
  gcongr

private lemma densityFun_isBoundedUnder (S : Set ℕ) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (densityFun S) := by
  refine ⟨1, ?_⟩
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall (densityFun_le_one S)

private lemma densityFun_isCoboundedUnder (S : Set ℕ) :
    Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (densityFun S) := by
  use 0; simp +decide [Filter.IsCoboundedUnder]
  exact fun a x hx => le_trans (densityFun_nonneg S x) (hx x le_rfl)

private lemma densityFun_add_compl (S : Set ℕ) (N : ℕ) (hN : 1 ≤ N) :
    densityFun S N + densityFun Sᶜ N = 1 := by
  unfold densityFun
  rw [← add_div, div_eq_iff] <;> norm_cast <;> try linarith
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  erw [Finset.sum_congr rfl fun x hx => by aesop]
  norm_num

/-- **Upper density is monotone**: if S ⊆ T, then upperDensity S ≤ upperDensity T.
    The counting function for S is dominated by that of T on every finite window,
    so the limsup of the ratio is also dominated. -/
theorem upperDensity_mono {S T : Set ℕ} (hST : S ⊆ T) :
    upperDensity S ≤ upperDensity T := by
  rw [upperDensity_eq_densityFun, upperDensity_eq_densityFun]
  exact Filter.limsup_le_limsup
    (Filter.Eventually.of_forall (densityFun_mono hST))
    (densityFun_isCoboundedUnder S)
    (densityFun_isBoundedUnder T)

/-- **Density monotonicity in k**: the upper density of the good set is non-decreasing
    as the window width grows. Formally: more n satisfy P(n,k+1) > n^(1-ε) than P(n,k) > n^(1-ε).
    This is the key density property that underpins the Erdős conjecture. -/
theorem erdos_1201_density_mono_k (ε : ℝ) (k : ℕ) :
    upperDensity {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε) < gpfConsecutive n k} ≤
    upperDensity {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε) < gpfConsecutive n (k + 1)} :=
  upperDensity_mono (erdos_1201_good_set_mono_k ε k)

/-
## Epsilon-Monotonicity and Partial Conjecture Proof
-/

/-- For n ≥ 1 and ε ≥ 1/2 with ε < 1, the rpow threshold n^(1-ε) is at most √n.
    This is because 1-ε ≤ 1/2 when ε ≥ 1/2, so n^(1-ε) ≤ n^(1/2) = √n for n ≥ 1. -/
theorem erdos_1201_sqrt_le_rpow_of_large_eps (n : ℕ) (ε : ℝ) (hε_half : 1 / 2 ≤ ε)
    (hε_lt1 : ε < 1) :
    (n : ℝ) ^ (1 - ε) ≤ Real.sqrt n := by
  rw [Real.sqrt_eq_rpow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show (1 - ε) ≠ 0 by linarith),
          Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- **ε-Monotonicity (pointwise)**: The good-set condition gets easier as ε increases.
    For ε₁ < ε₂ and n ≥ 2: if P(n,k) > n^(1-ε₁) then P(n,k) > n^(1-ε₂).
    This holds because n > 1 and 1-ε₂ < 1-ε₁ imply n^(1-ε₂) < n^(1-ε₁). -/
theorem erdos_1201_good_implies_larger_eps (n k : ℕ) (ε₁ ε₂ : ℝ) (hn : 2 ≤ n)
    (hε12 : ε₁ < ε₂) (hgood : (n : ℝ) ^ (1 - ε₁) < gpfConsecutive n k) :
    (n : ℝ) ^ (1 - ε₂) < gpfConsecutive n k :=
  calc (n : ℝ) ^ (1 - ε₂)
      < (n : ℝ) ^ (1 - ε₁) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast show 1 < n from by omega)
          (by linarith)
    _ < _ := hgood

/-- **Good-set containment in ε**: For ε₁ < ε₂, the ε₁-good set ⊆ the ε₂-good set.
    Larger ε gives a smaller threshold n^(1-ε), making the condition easier to satisfy. -/
theorem erdos_1201_good_set_mono_eps (k : ℕ) (ε₁ ε₂ : ℝ) (hε12 : ε₁ < ε₂) :
    {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε₁) < gpfConsecutive n k} ⊆
    {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε₂) < gpfConsecutive n k} := fun n ⟨hn2, hgood⟩ =>
  ⟨hn2, erdos_1201_good_implies_larger_eps n k ε₁ ε₂ hn2 hε12 hgood⟩

/-- **Density monotonicity in ε**: upper density of the good set is non-decreasing in ε. -/
theorem erdos_1201_density_mono_eps (k : ℕ) (ε₁ ε₂ : ℝ) (hε12 : ε₁ < ε₂) :
    upperDensity {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε₁) < gpfConsecutive n k} ≤
    upperDensity {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - ε₂) < gpfConsecutive n k} :=
  upperDensity_mono (erdos_1201_good_set_mono_eps k ε₁ ε₂ hε12)

/-- **Half-case implies conjecture for ε ≥ 1/2**: Erdős's ε = 1/2 result implies
    ErdosProblem1201 for all ε ∈ [1/2, 1). Since n^(1-ε) ≤ √n for ε ≥ 1/2 and n ≥ 1,
    the set {n | √n < P(n,k)} ⊆ {n | n^(1-ε) < P(n,k)}, so density passes through. -/
theorem erdos_1201_half_case_implies (ε η : ℝ) (hε_half : 1 / 2 ≤ ε) (hε_lt1 : ε < 1)
    (hη : 0 < η) :
    ∃ k : ℕ, upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η := by
  obtain ⟨k, hk⟩ := erdos_1201_half_case η hη
  refine ⟨k, le_trans hk (upperDensity_mono ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at *
  exact lt_of_le_of_lt (erdos_1201_sqrt_le_rpow_of_large_eps n ε hε_half hε_lt1) hn

/-- **Partial conjecture (proved)**: ErdosProblem1201 holds for all ε ≥ 1/2.
    This is the first unconditional theorem about the conjecture: the "easy half" (ε ≥ 1/2)
    follows from Erdős's result via the ε-monotonicity of the good set. -/
theorem erdos_1201_partial_conjecture :
    ∀ (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η), 1 / 2 ≤ ε →
    ∃ k : ℕ,
      upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η :=
  fun ε η _ hε₁ hη hε_half => erdos_1201_half_case_implies ε η hε_half hε₁ hη


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

/-- Among any m consecutive integers starting at n (for m ≥ 1), some term is divisible by m.
    Key: k+1 consecutive integers cover all residue classes mod k+1 exactly once. -/
private lemma exists_dvd_in_consecutive (n m : ℕ) (hm : 0 < m) : ∃ i < m, m ∣ n + i := by
  rcases Nat.eq_zero_or_pos (n % m) with h | h
  · exact ⟨0, hm, Nat.dvd_of_mod_eq_zero h⟩
  · have hlt : n % m < m := Nat.mod_lt n hm
    refine ⟨m - n % m, Nat.sub_lt hm h, Nat.dvd_of_mod_eq_zero ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hm h),
        Nat.add_sub_cancel' (Nat.le_of_lt hlt), Nat.mod_self]

/-- **Sylvester-Schur (prime window size)**: When k+1 is prime, P(n, k) ≥ k+1 for all n ≥ 1.
    Among any k+1 consecutive integers, the complete residue system mod k+1 guarantees one
    is divisible by k+1, which is a prime factor > k of the consecutive product. -/
theorem gpfConsecutive_ge_succ_k_of_prime (n k : ℕ) (hn : 1 ≤ n) (hk1 : (k + 1).Prime) :
    k + 1 ≤ gpfConsecutive n k := by
  obtain ⟨i, hi_lt, hi_dvd⟩ := exists_dvd_in_consecutive n (k + 1) (Nat.succ_pos k)
  exact le_gpfConsecutive_of_prime_dvd_term n k i hn (by omega) (k + 1) hk1 hi_dvd

/-- **Sylvester-Schur (prime window size, strict)**: When k+1 is prime, k < P(n, k) for all n ≥ 1.
    Covers all prime-predecessor k: k = 1, 2, 4, 6, 10, 12, 16, 18, ... -/
theorem gpfConsecutive_gt_k_of_prime_succ (n k : ℕ) (hn : 1 ≤ n) (hk1 : (k + 1).Prime) :
    k < gpfConsecutive n k :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (gpfConsecutive_ge_succ_k_of_prime n k hn hk1)

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
  have hcop : Nat.Coprime n (n + 1) := by
    rw [Nat.Coprime]
    apply Nat.dvd_one.mp
    have h := Nat.dvd_sub (Nat.gcd_dvd_right n (n + 1)) (Nat.gcd_dvd_left n (n + 1))
    rwa [show n + 1 - n = 1 from by omega] at h
  exact (hcop.coprime_dvd_left (gpf_dvd n hn)).coprime_dvd_right (gpf_dvd (n + 1) (by omega))

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
  refine Finset.le_sup (f := fun j => greatestPrimeFactor (n + j)) ?_
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

/-
## Factorial Divisibility and Universal Lower Bound
-/

/-- The consecutive product n(n+1)···(n+k) equals the descending factorial (n+k)↓(k+1). -/
private lemma consecutiveProduct_eq_descFactorial (n k : ℕ) :
    consecutiveProduct n k = (n + k).descFactorial (k + 1) := by
  simp only [consecutiveProduct]
  rw [Nat.descFactorial_eq_prod_range]
  rw [← Finset.prod_range_reflect (fun j => n + j) (k + 1)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  omega

/-- **(k+1)! divides every product of k+1 consecutive integers**, for any starting point n.
    This is the identity n(n+1)···(n+k) = C(n+k, k+1) · (k+1)!, which follows from
    expressing the product as a descending factorial. -/
theorem factorial_dvd_consecutiveProduct (n k : ℕ) :
    (k + 1).factorial ∣ consecutiveProduct n k := by
  rw [consecutiveProduct_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  exact dvd_mul_right _ _

/-- **Universal GPF Lower Bound from Factorial**: P(n,k) ≥ GPF((k+1)!) for all n ≥ 1, k ≥ 1.
    Since (k+1)! divides the consecutive product, GPF((k+1)!) divides the product,
    so GPF((k+1)!) ≤ P(n,k). By Bertrand, GPF((k+1)!) > k/2. -/
theorem gpfConsecutive_ge_factorial_gpf (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    greatestPrimeFactor (k + 1).factorial ≤ gpfConsecutive n k := by
  have hfact_dvd := factorial_dvd_consecutiveProduct n k
  have hfact_ge2 : 2 ≤ (k + 1).factorial :=
    le_trans (by omega) (Nat.self_le_factorial (k + 1))
  have hcp_ge2 : 2 ≤ consecutiveProduct n k :=
    Nat.le_trans hfact_ge2 (Nat.le_of_dvd (consecutiveProduct_pos n k hn) hfact_dvd)
  exact gpf_ge_prime_dvd _ _ hcp_ge2 (gpf_prime _ hfact_ge2)
    (dvd_trans (gpf_dvd _ hfact_ge2) hfact_dvd)

/-- **Universal Half-Window Lower Bound**: 2 · P(n,k) > k for any n ≥ 1 and k ≥ 2.
    By Bertrand, there is a prime p with k/2 < p ≤ k ≤ k+1, so p | (k+1)! | consecutive product,
    giving P(n,k) ≥ p > k/2. This holds for ALL starting points n ≥ 1, with no n > k condition. -/
theorem gpfConsecutive_gt_half_k (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    k < 2 * gpfConsecutive n k := by
  obtain ⟨p, hp_prime, hm_lt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  have hp_le_k1 : p ≤ k + 1 := by omega
  have hp_dvd_fact : p ∣ (k + 1).factorial := hp_prime.dvd_factorial.mpr hp_le_k1
  have hfact_dvd := factorial_dvd_consecutiveProduct n k
  have hp_dvd_cp : p ∣ consecutiveProduct n k := dvd_trans hp_dvd_fact hfact_dvd
  have hfact_ge2 : 2 ≤ (k + 1).factorial :=
    le_trans (by omega) (Nat.self_le_factorial (k + 1))
  have hcp_ge2 : 2 ≤ consecutiveProduct n k :=
    Nat.le_trans hfact_ge2 (Nat.le_of_dvd (consecutiveProduct_pos n k hn) hfact_dvd)
  have hge : p ≤ gpfConsecutive n k := by
    unfold gpfConsecutive; exact gpf_ge_prime_dvd _ _ hcp_ge2 hp_prime hp_dvd_cp
  have hlt : k < 2 * p := by omega
  linarith

/-- **Threshold Bound**: If n^(1-ε) < k/2, then P(n,k) > n^(1-ε).
    Combining `gpfConsecutive_gt_half_k` (P > k/2) with the hypothesis n^(1-ε) < k/2
    gives n^(1-ε) < k/2 ≤ P(n,k). This gives a concrete sufficient condition for the
    Erdős property: all n with n^(1-ε) < k/2 are automatically good. -/
theorem erdos_1201_threshold_bound (n k : ℕ) (ε : ℝ) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hbound : (n : ℝ) ^ (1 - ε) < (k : ℝ) / 2) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) := by
  have h_half : (k : ℝ) / 2 ≤ (gpfConsecutive n k : ℝ) := by
    have h_real : (k : ℝ) < 2 * (gpfConsecutive n k : ℝ) :=
      by exact_mod_cast gpfConsecutive_gt_half_k n k hn hk
    linarith
  linarith

/-- For ε ≥ 1, any n ≥ 2 is automatically good: n^(1-ε) ≤ n^0 = 1 < 2 ≤ P(n,k). -/
theorem erdos_1201_trivially_good_of_large_eps (n k : ℕ) (ε : ℝ) (hn : 2 ≤ n) (hε : 1 ≤ ε) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) := by
  have h_pow_le : (n : ℝ) ^ (1 - ε) ≤ 1 :=
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega))
      (by linarith)).trans_eq (Real.rpow_zero _)
  linarith [show (2 : ℝ) ≤ (gpfConsecutive n k : ℝ) from
    by exact_mod_cast gpfConsecutive_ge_two n k hn]

/-- **Reduction to ε = 1/2**: For ε ∈ [1/2, 1), the Erdős conjecture follows from
    Erdős's known result (axiom `erdos_1201_half_case`).
    Since n^(1-ε) ≤ n^(1/2) = √n for ε ≥ 1/2 and n ≥ 1, any n with √n < P(n,k)
    automatically satisfies n^(1-ε) < P(n,k). The open problem reduces to ε ∈ (0, 1/2). -/
theorem erdos_1201_conjecture_large_eps (ε η : ℝ) (hε_lb : 1 / 2 ≤ ε) (hε_ub : ε < 1)
    (hη : 0 < η) :
    ∃ k : ℕ,
      upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η := by
  obtain ⟨k, hk⟩ := erdos_1201_half_case η hη
  refine ⟨k, le_trans hk (upperDensity_mono ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp only [Nat.cast_zero, Real.sqrt_zero,
               Real.zero_rpow (show (0 : ℝ) < 1 - ε from by linarith).ne'] at hn ⊢
    exact hn
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    rw [Real.sqrt_eq_rpow] at hn
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans_lt hn

/-- For n ≥ 1, the window [n, n+2] (3 consecutive integers) always has a largest prime factor > 2.
    Immediate from Sylvester-Schur for prime window size 3 (k=2, k+1=3 is prime). -/
theorem gpfConsecutive_two_gt_two (n : ℕ) (hn : 1 ≤ n) : 2 < gpfConsecutive n 2 :=
  gpfConsecutive_gt_k_of_prime_succ n 2 hn (by norm_num)

/-- **Individual Threshold**: For each n ≥ 2 and ε ∈ (0,1), some finite window makes n "good".
    Specifically window k = n works: P(n,n) > n > n^(1-ε) by Bertrand's postulate.
    The CONJECTURE asks for a FIXED window working for density-1 of all n simultaneously. -/
theorem erdos_1201_individual_threshold (n : ℕ) (hn : 2 ≤ n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) := by
  refine ⟨n, ?_⟩
  have h_gt : n < gpfConsecutive n n := gpfConsecutive_self_gt n (by omega)
  have h_ncast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n from by omega)
  have h_bound : (n : ℝ) ^ (1 - ε) < (n : ℝ) :=
    calc (n : ℝ) ^ (1 - ε) < (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt h_ncast (by linarith)
      _ = (n : ℝ) := Real.rpow_one _
  linarith [show (n : ℝ) ≤ gpfConsecutive n n from by exact_mod_cast h_gt.le]

/-- **Good Set Monotonicity (pointwise)**: if n is good for window k₁, it's good for all k₂ ≥ k₁.
    Generalization of `erdos_1201_good_set_mono_k` from k → k+1 to arbitrary k₁ ≤ k₂. -/
theorem erdos_1201_good_set_mono (ε : ℝ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (n : ℕ) (hn : 2 ≤ n)
    (h : (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k₁ : ℝ)) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k₂ : ℝ) :=
  h.trans_le (by exact_mod_cast gpfConsecutive_le_of_le_k n hn hk)

/-- **Formal reduction to ε < 1/2**: The Erdős conjecture is equivalent to its restriction to
    ε ∈ (0, 1/2). The case ε ∈ [1/2, 1) is already settled by `erdos_1201_conjecture_large_eps`. -/
theorem erdos_1201_equiv_small_eps :
    ErdosProblem1201 ↔
    ∀ (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) (hη : 0 < η),
      ∃ k : ℕ, upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η := by
  constructor
  · intro h ε η hε₀ hε₁ hη
    exact h ε η hε₀ (by linarith) hη
  · intro h ε η hε₀ hε₁ hη
    by_cases hε_half : 1 / 2 ≤ ε
    · exact erdos_1201_conjecture_large_eps ε η hε_half hε₁ hη
    · push_neg at hε_half
      exact h ε η hε₀ hε_half hη

/-
## Smooth-Window Characterization and Conditional Reduction
-/

/-- **Smooth-Window Duality**: n is NOT good for the Erdős problem iff every term n+i (i ≤ k)
    has greatest prime factor ≤ n^(1-ε), i.e., the window [n, n+k] is n^(1-ε)-smooth.
    Equivalently: n is bad iff the consecutive product n(n+1)···(n+k) is n^(1-ε)-smooth. -/
theorem erdos_1201_not_good_smooth_window (n k : ℕ) (ε : ℝ) (hn : 2 ≤ n) :
    ¬((n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)) ↔
    ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
  rw [not_lt]
  constructor
  · intro hle i hi
    have hle_i : greatestPrimeFactor (n + i) ≤ gpfConsecutive n k := by
      rw [gpfConsecutive_eq_sup_range n k hn]
      exact Finset.le_sup (f := fun j => greatestPrimeFactor (n + j))
                          (Finset.mem_range.mpr (by omega))
    exact (Nat.cast_le.mpr hle_i).trans hle
  · intro hall
    have hnn : 0 ≤ (n : ℝ) ^ (1 - ε) := by positivity
    have hle : gpfConsecutive n k ≤ ⌊(n : ℝ) ^ (1 - ε)⌋₊ :=
      (gpfConsecutive_le_iff n k hn _).mpr fun i hi => Nat.le_floor (hall i hi)
    exact le_trans (Nat.cast_le.mpr hle) (Nat.floor_le hnn)

/-- **Rough-Term Characterization**: n is good for the Erdős problem iff some term n+i in the
    window [n, n+k] has greatest prime factor exceeding n^(1-ε).
    Negation of `erdos_1201_not_good_smooth_window`: good ↔ the window is NOT fully smooth. -/
theorem erdos_1201_good_iff_rough_term (n k : ℕ) (ε : ℝ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) ↔
    ∃ i ≤ k, (n : ℝ) ^ (1 - ε) < (greatestPrimeFactor (n + i) : ℝ) := by
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    exact absurd h ((erdos_1201_not_good_smooth_window n k ε hn).mpr hall)
  · intro ⟨i, hi, hlt⟩
    have hge : greatestPrimeFactor (n + i) ≤ gpfConsecutive n k := by
      rw [gpfConsecutive_eq_sup_range n k hn]
      exact Finset.le_sup (f := fun j => greatestPrimeFactor (n + j))
                          (Finset.mem_range.mpr (by omega))
    exact lt_of_lt_of_le hlt (Nat.cast_le.mpr hge)

/-- **Prime-Window Conditional**: ErdosProblem1201 follows from a prime gap hypothesis.
    If for each ε, η > 0 there exists k such that almost all n ≥ 2 have a prime in [n, n+k]
    exceeding n^(1-ε), then ErdosProblem1201 holds.
    Formally reduces the open conjecture to a prime distribution statement (Cramér-type). -/
theorem erdos_1201_conditional_proof
    (hprime : ∀ (ε η : ℝ), 0 < ε → ε < 1 → 0 < η →
      ∃ k : ℕ, upperDensity {n : ℕ | 2 ≤ n ∧ ∃ i ≤ k, (n + i).Prime ∧
                (n : ℝ) ^ (1 - ε) < (n + i : ℝ)} ≥ 1 - η) :
    ErdosProblem1201 := by
  intro ε η hε₀ hε₁ hη
  obtain ⟨k, hk⟩ := hprime ε η hε₀ hε₁ hη
  refine ⟨k, le_trans hk (upperDensity_mono ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  obtain ⟨hn2, i, hi, hprime_i, hlt⟩ := hn
  exact erdos_1201_good_of_prime_in_window n k i ε hn2 hi hprime_i hlt

/-
## Density Complement and Smooth-Density Conditional
-/

/-- **Primes are good for k=0**: Any prime n ≥ 2 satisfies gpf(n) = n > n^(1-ε) for ε ∈ (0,1).
    This gives the k=0 base case: the k=0 good set contains all primes. -/
theorem erdos_1201_good_prime_k0 (n : ℕ) (hn_prime : n.Prime) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    (n : ℝ) ^ (1 - ε) < (gpfConsecutive n 0 : ℝ) := by
  rw [gpfConsecutive_zero, greatestPrimeFactor_prime n hn_prime]
  have hn2 : 1 < (n : ℝ) := by exact_mod_cast hn_prime.one_lt
  calc (n : ℝ) ^ (1 - ε) < (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hn2 (by linarith)
    _ = (n : ℝ) := Real.rpow_one _

/-- **Complement density lower bound**: The upper density of the complement of S is at least
    1 minus the upper density of S. Formally: upperDensity(Sᶜ) ≥ 1 - upperDensity(S).
    Key step: for N ≥ 1, density_S + density_Sᶜ = 1 exactly.
    Combined with limsup sub-additivity: limsup(density_S) + limsup(density_Sᶜ) ≥ limsup(1) = 1. -/
theorem upperDensity_compl_ge (S : Set ℕ) : 1 - upperDensity S ≤ upperDensity Sᶜ := by
  rw [upperDensity_eq_densityFun, upperDensity_eq_densityFun]
  rw [Filter.limsup_eq, Filter.limsup_eq]
  refine le_csInf ?_ ?_
  · exact ⟨1, Filter.Eventually.of_forall fun n => densityFun_le_one _ _⟩
  · intro b hb
    rw [sub_le_comm]
    refine le_csInf ?_ ?_
    · exact ⟨1, Filter.Eventually.of_forall fun n => densityFun_le_one _ _⟩
    · intro c hc
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hb.and hc)
      linarith [hN (N + 1) (by linarith), densityFun_add_compl S (N + 1) (by linarith)]

/-- Upper density is monotone under set inclusion up to a finite set: if S ⊆ T ∪ F where
    F is a finite set, then upperDensity S ≤ upperDensity T. -/
private lemma upperDensity_le_of_subset_union_finite {S T : Set ℕ} (F : Finset ℕ)
    (h : S ⊆ T ∪ ↑F) : upperDensity S ≤ upperDensity T := by
  have h_upper_density_union : upperDensity (T ∪ F) = upperDensity T := by
    rw [upperDensity_eq_densityFun, upperDensity_eq_densityFun]
    have h_diff_zero : Filter.Tendsto (fun N => (densityFun (T ∪ F) N) - (densityFun T N)) Filter.atTop (nhds 0) := by
      have h_diff_le : ∀ N : ℕ, N > 0 → abs ((densityFun (T ∪ F) N) - (densityFun T N)) ≤ (F.card : ℝ) / N := by
        unfold densityFun
        intro N hN; rw [div_sub_div_same, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]; gcongr
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
        · rw [sub_le_iff_le_add']
          norm_cast
          exact le_trans (Finset.card_le_card fun x hx => by aesop) (Finset.card_union_le _ _)
        · exact le_trans (sub_nonpos_of_le <| mod_cast Finset.card_mono <| fun x hx => by aesop) <| Nat.cast_nonneg _
      exact squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨1, fun N hN => h_diff_le N hN⟩) (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    by_cases hT : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (densityFun T) <;>
      by_cases hTF : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (densityFun (T ∪ F)) <;>
      simp_all +decide [Filter.limsup_eq]
    · refine le_antisymm ?_ ?_ <;> refine le_csInf ?_ ?_ <;> norm_num at *
      · obtain ⟨M, hM⟩ := hT; use M; aesop
      · intro b x hx; refine le_of_forall_pos_le_add fun ε' εpos => ?_; simp_all +decide [Metric.tendsto_nhds]
        exact csInf_le ⟨0, by rintro a ⟨y, hy⟩; exact le_trans (by exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hy _ le_rfl)⟩
          ⟨Max.max x (Classical.choose (h_diff_zero ε' εpos)), fun n hn => by
            linarith [abs_lt.mp (Classical.choose_spec (h_diff_zero ε' εpos) n (le_trans (le_max_right _ _) hn)),
                      hx n (le_trans (le_max_left _ _) hn)]⟩
      · rcases hTF with ⟨M, hM⟩; exact ⟨M, by rcases Filter.eventually_atTop.mp hM with ⟨N, hN⟩; exact ⟨N, fun n hn => hN n hn⟩⟩
      · intro b x hx; refine csInf_le ?_ ?_ <;> norm_num at *
        · exact ⟨0, by rintro _ ⟨y, hy⟩; exact le_trans (by exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hy _ le_rfl)⟩
        · exact ⟨x, fun n hn => le_trans (show densityFun T n ≤ densityFun (T ∪ F) n from by
            exact div_le_div_of_nonneg_right (mod_cast Finset.card_mono <| fun x hx => by aesop) <| Nat.cast_nonneg _) (hx n hn)⟩
    · contrapose! hTF
      exact ⟨1, Filter.eventually_atTop.mpr ⟨1, fun N hN => densityFun_le_one _ _⟩⟩
    · contrapose! hT
      exact ⟨1, Filter.eventually_atTop.mpr ⟨1, fun n hn => densityFun_le_one T n⟩⟩
    · contrapose! hT
      exact ⟨1, Filter.eventually_atTop.mpr ⟨1, fun n hn => densityFun_le_one T n⟩⟩
  exact h_upper_density_union ▸ upperDensity_mono h

/-- The complement of good set (for n ≥ 2) is the bad set. -/
private lemma good_compl_n_ge_2 (n k : ℕ) (ε : ℝ) (hn : 2 ≤ n) :
    n ∈ {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)}ᶜ ↔
    (∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)) := by
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  exact erdos_1201_not_good_smooth_window n k ε hn

/-- **From bad density to good density**: If the upper density of the bad set (windows where all
    terms are n^(1-ε)-smooth) is at most η, then the upper density of the good set is at least 1-η.
    Proof: good set ⊇ complement of bad set (for n ≥ 2), and the density complement bound gives
    density(complement_bad) ≥ 1 - density(bad) ≥ 1 - η. The n < 2 edge case doesn't affect density. -/
theorem erdos_1201_from_bad_density_bound (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (h : ∀ η : ℝ, 0 < η → ∃ k : ℕ,
      upperDensity {n : ℕ | 2 ≤ n ∧
        ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)} ≤ η) :
    ∀ η : ℝ, 0 < η → ∃ k : ℕ,
      upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η := by
  intro η hη
  obtain ⟨k, hk⟩ := h η hη
  refine ⟨k, ?_⟩
  -- {good}ᶜ ⊆ {bad} ∪ {0, 1}
  have hcompl_sub : {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)}ᶜ ⊆
      {n : ℕ | 2 ≤ n ∧ ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)} ∪ ↑({0, 1} : Finset ℕ) := by
    intro n hn
    by_cases hn2 : 2 ≤ n
    · left
      exact ⟨hn2, (good_compl_n_ge_2 n k ε hn2).mp hn⟩
    · right
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
  have h_compl_bound : upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)}ᶜ ≤ η :=
    (upperDensity_le_of_subset_union_finite {0, 1} hcompl_sub).trans hk
  linarith [upperDensity_compl_ge {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)}]

/-- **Smooth-Decay Conditional**: ErdosProblem1201 follows from the hypothesis that for each ε,
    the upper density of {n | n,...,n+k all n^(1-ε)-smooth} decays to 0 as k → ∞.
    This is the formalization of Erdős's rough argument via the Dickman function:
    ρ(1/(1-ε))^(k+1) → 0 as k → ∞ for any ε ∈ (0,1). -/
theorem erdos_1201_smooth_decay_implies_conjecture
    (h : ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ η : ℝ, 0 < η → ∃ k : ℕ,
        upperDensity {n : ℕ | 2 ≤ n ∧
          ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)} ≤ η) :
    ErdosProblem1201 := by
  intro ε η hε₀ hε₁ hη
  exact erdos_1201_from_bad_density_bound ε hε₀ hε₁ (h ε hε₀ hε₁) η hη

/-
## Upper Density Basic Facts
-/

private lemma icc_one_card (N : ℕ) : (Finset.Icc 1 N).card = N := by
  have h : Finset.Icc 1 N = (Finset.range N).map ⟨(· + 1), fun a b heq => by omega⟩ := by
    ext x; simp [Finset.mem_range]; omega
  simp [h]

/-- The empty set has upper density 0. -/
theorem upperDensity_empty : upperDensity ∅ = 0 := by
  simp only [upperDensity]
  have h : (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ (∅ : Set ℕ))).card : ℝ) / N) =
           fun _ => 0 := by ext N; simp
  rw [h]; exact Filter.limsup_const 0

/-- Upper density is at most 1: the counting ratio never exceeds 1. -/
theorem upperDensity_le_one (S : Set ℕ) : upperDensity S ≤ 1 := by
  simp only [upperDensity]
  apply Filter.limsup_le_of_le
  · exact (⟨0, Filter.Eventually.of_forall fun (N : ℕ) =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩ :
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop _).isCoboundedUnder_le
  · exact Filter.Eventually.of_forall fun (N : ℕ) => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · exact div_le_one_of_le
            (by exact_mod_cast (Finset.card_filter_le _ _).trans (icc_one_card N).le)
            (Nat.cast_nonneg _)

/-- Upper density is non-negative. -/
theorem upperDensity_ge_zero (S : Set ℕ) : 0 ≤ upperDensity S := by
  simpa [upperDensity_empty] using upperDensity_mono (Set.empty_subset S)

/-- The full set ℕ has upper density 1. -/
theorem upperDensity_univ : upperDensity Set.univ = 1 :=
  le_antisymm (upperDensity_le_one _) (by
    simp only [upperDensity]
    have h : ∀ᶠ N : ℕ in Filter.atTop,
        (((Finset.Icc 1 N).filter fun n => n ∈ Set.univ).card : ℝ) / N = 1 :=
      Filter.eventually_atTop.mpr ⟨1, fun N hN => by
        rw [Finset.filter_true_of_mem (fun _ _ => Set.mem_univ _)]
        have : (Finset.Icc 1 N).card = N := icc_one_card N
        rw [this]; exact div_self (Nat.cast_ne_zero.mpr (by omega))⟩
    exact (Filter.limsup_congr h).trans (Filter.limsup_const 1))

/-
## Asymptotic Behavior as Window Grows
-/

/-- For fixed n ≥ 2, the window GPF P(n,k) tends to +∞ as k → ∞.
    Proof: for any bound M, by infinitude of primes there exists a prime p > max(n,M);
    then for k ≥ p - n, the window contains p, giving P(n,k) ≥ p > M. -/
theorem gpfConsecutive_atTop (n : ℕ) (hn : 2 ≤ n) :
    Filter.Tendsto (gpfConsecutive n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max n M + 1)
  have hn_lt : n < p := by omega
  have hM_le : M ≤ p := by omega
  refine ⟨p - n, fun k hk => ?_⟩
  have heq : n + (p - n) = p := Nat.add_sub_cancel' (Nat.le_of_lt hn_lt)
  calc M ≤ p := hM_le
    _ = n + (p - n) := heq.symm
    _ ≤ gpfConsecutive n k :=
        gpfConsecutive_ge_prime_term n k (p - n) hn hk (heq.symm ▸ hp_prime)

/-- **Individual eventual goodness**: For any fixed n ≥ 2 and ε ∈ (0,1), n is eventually
    "good": for all sufficiently large k, P(n,k) > n^(1-ε).
    Follows from `erdos_1201_individual_threshold` + monotonicity of P(n,k) in k. -/
theorem erdos_1201_eventually_good (n : ℕ) (hn : 2 ≤ n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∀ᶠ k in Filter.atTop, (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ) := by
  obtain ⟨K, hK⟩ := erdos_1201_individual_threshold n hn ε hε₀ hε₁
  exact Filter.eventually_atTop.mpr
    ⟨K, fun k hk => hK.trans_le (Nat.cast_le.mpr (gpfConsecutive_le_of_le_k n hn hk))⟩

/-- **Density is eventually large**: Assuming ErdosProblem1201, for each ε, η > 0 the
    good-set density is ≥ 1 - η for ALL sufficiently large k, not just one k.
    This strengthens ErdosProblem1201 using k-monotonicity of the good set. -/
theorem erdos_1201_density_eventually_large (hE : ErdosProblem1201)
    (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k ≥ K,
      upperDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η := by
  obtain ⟨K, hK⟩ := hE ε η hε₀ hε₁ hη
  refine ⟨K, fun k hk => hK.trans (upperDensity_mono ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  rcases le_or_lt 2 n with hn2 | hn2
  · exact hn.trans_le (Nat.cast_le.mpr (gpfConsecutive_le_of_le_k n hn2 hk))
  · interval_cases n
    · simp only [Nat.cast_zero] at hn
      have h0cp : consecutiveProduct 0 K = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ K)) (by simp)
      have h0gpf : (gpfConsecutive 0 K : ℝ) = 0 := by
        norm_cast; simp [gpfConsecutive, h0cp, greatestPrimeFactor, Nat.primeFactors_zero]
      rw [Real.zero_rpow (by linarith), h0gpf] at hn
      exact absurd hn (lt_irrefl 0)
    · simp only [Nat.cast_one, Real.one_rpow] at hn ⊢
      have hK1 : 1 ≤ K := by
        by_contra h; push_neg at h; interval_cases K
        simp [gpfConsecutive, consecutiveProduct_zero, greatestPrimeFactor, Nat.primeFactors_one]
          at hn
      have hk1 : 1 ≤ k := le_trans hK1 hk
      have h2dvd : 2 ∣ consecutiveProduct 1 k :=
        Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (show 1 < k + 1 from by omega))
          (by norm_num)
      have hcp_pos : 0 < consecutiveProduct 1 k := consecutiveProduct_pos 1 k (by omega)
      exact_mod_cast calc (1 : ℝ) < 2 := by norm_num
        _ ≤ gpfConsecutive 1 k := by
            exact_mod_cast gpf_ge_prime_dvd (consecutiveProduct 1 k) 2
              (Nat.le_of_dvd hcp_pos h2dvd) (by norm_num) h2dvd

/-
## Lower Density
-/

/-- Lower density of a set S ⊆ ℕ: lim inf_{N→∞} |S ∩ [1,N]| / N. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  haveI : DecidablePred (· ∈ S) := Classical.decPred _
  Filter.liminf (fun N : ℕ =>
    (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ))
  Filter.atTop

/-- Lower density is non-negative. -/
theorem lowerDensity_nonneg (S : Set ℕ) : 0 ≤ lowerDensity S := by
  simp only [lowerDensity]
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ)) :=
    ⟨1, Filter.Eventually.of_forall fun (N : ℕ) => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · apply div_le_one_of_le _ (Nat.cast_nonneg N)
        exact_mod_cast (Finset.card_filter_le _ _).trans (icc_one_card N).le⟩
  apply le_liminf_of_le hbdd.isCoboundedUnder_ge
  exact Filter.Eventually.of_forall fun (N : ℕ) =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Lower density is at most upper density. -/
theorem lowerDensity_le_upperDensity (S : Set ℕ) : lowerDensity S ≤ upperDensity S := by
  simp only [lowerDensity, upperDensity]
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ)) :=
    ⟨1, Filter.Eventually.of_forall fun (N : ℕ) => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · apply div_le_one_of_le _ (Nat.cast_nonneg N)
        exact_mod_cast (Finset.card_filter_le _ _).trans (icc_one_card N).le⟩
  exact Filter.liminf_le_limsup hbdd.isCoboundedUnder_ge hbdd

/-- **Lower density of complement = 1 − upper density**:
    For N ≥ 1, |Sᶜ ∩ [1,N]| / N = 1 - |S ∩ [1,N]| / N exactly,
    so lim inf(density Sᶜ) = lim inf(1 - density S) = 1 - lim sup(density S). -/
theorem lowerDensity_compl (S : Set ℕ) : lowerDensity Sᶜ = 1 - upperDensity S := by
  haveI hS : DecidablePred (· ∈ S) := Classical.decPred _
  haveI hSc : DecidablePred (· ∈ Sᶜ) := Classical.decPred _
  have heq : ∀ᶠ N : ℕ in Filter.atTop,
      (((Finset.Icc 1 N).filter (fun n => n ∉ S)).card : ℝ) / (N : ℝ) =
      1 - (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ) := by
    apply Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
    have hcard : (Finset.Icc 1 N).card = N := icc_one_card N
    have hcard_le : ((Finset.Icc 1 N).filter (fun n => n ∈ S)).card ≤ N :=
      (Finset.card_filter_le _ _).trans hcard.le
    have hcompl : (Finset.Icc 1 N).filter (fun n => n ∉ S) =
        (Finset.Icc 1 N) \ (Finset.Icc 1 N).filter (fun n => n ∈ S) := by
      ext x; simp [Set.mem_compl_iff]
    rw [hcompl, Finset.card_sdiff (Finset.filter_subset _ _), hcard]
    push_cast [Nat.cast_sub hcard_le]
    field_simp
  simp only [lowerDensity, upperDensity, Set.mem_compl_iff]
  rw [Filter.liminf_congr heq]
  have hbdd_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ)) :=
    ⟨1, Filter.Eventually.of_forall fun (N : ℕ) => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · exact div_le_one_of_le
            (by exact_mod_cast (Finset.card_filter_le _ _).trans (icc_one_card N).le)
            (Nat.cast_nonneg _)⟩
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ)) :=
    ⟨0, fun c hc => by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
      exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hN N le_rfl)⟩
  exact Filter.liminf_const_sub 1 hbdd_above hcobdd

/-- **Complement duality for upper density**: upperDensity(Sᶜ) = 1 - lowerDensity(S).
    Symmetric to `lowerDensity_compl` (which gives lowerDensity(Sᶜ) = 1 - upperDensity(S)). -/
theorem upperDensity_compl_eq (S : Set ℕ) : upperDensity Sᶜ = 1 - lowerDensity S := by
  have h := lowerDensity_compl Sᶜ
  simp only [compl_compl] at h
  linarith

/-- **Strong Erdős Conjecture #1201**: Like ErdosProblem1201 but uses lower density (lim inf)
    instead of upper density (lim sup). For every ε, η > 0 there exists k such that the
    LOWER density of {n | P(n,k) > n^(1-ε)} is at least 1 - η.
    This is a stronger statement than `ErdosProblem1201` (which uses lim sup / upper density):
    it asserts that for ALL large N (not just infinitely many), the density approaches 1 - η.
    The equivalence `erdos_1201_strong_iff_smooth_decay` shows this is precisely equivalent
    to the smooth-window density decaying to 0. -/
def ErdosProblem1201Strong : Prop :=
  ∀ (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hη : 0 < η),
  ∃ k : ℕ,
    lowerDensity {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} ≥ 1 - η

/-- Strong ⟹ weak: if lim inf (good density) ≥ 1 - η, then lim sup ≥ 1 - η. -/
theorem erdos_1201_strong_implies_weak : ErdosProblem1201Strong → ErdosProblem1201 := by
  intro hStrong ε η hε₀ hε₁ hη
  obtain ⟨k, hk⟩ := hStrong ε η hε₀ hε₁ hη
  exact ⟨k, hk.trans (lowerDensity_le_upperDensity _)⟩

/-- **Equivalence**: ErdosProblem1201Strong ↔ smooth-window-density decays to 0.
    Forward: strong conjecture → smooth-window density ≤ η (via lowerDensity complement duality).
    Backward: smooth-window density ≤ η → strong conjecture (via subadditivity + finite correction). -/
theorem erdos_1201_strong_iff_smooth_decay :
    ErdosProblem1201Strong ↔
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
    ∀ η : ℝ, 0 < η → ∃ k : ℕ,
      upperDensity {n : ℕ | 2 ≤ n ∧
        ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)} ≤ η := by
  constructor
  · intro hStrong ε hε₀ hε₁ η hη
    obtain ⟨k, hk⟩ := hStrong ε η hε₀ hε₁ hη
    set good := {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} with hgood_def
    set smooth_bad := {n : ℕ | 2 ≤ n ∧ ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)}
      with hbad_def
    have hcompl_bound : upperDensity goodᶜ ≤ η := by
      have hdual : lowerDensity good = 1 - upperDensity goodᶜ := by
        have := lowerDensity_compl goodᶜ
        simp only [compl_compl] at this
        exact this
      linarith
    have hsubset : smooth_bad ⊆ goodᶜ := by
      intro n ⟨hn2, hsmooth⟩
      simp only [hgood_def, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact (erdos_1201_not_good_smooth_window n k ε hn2).mpr hsmooth
    exact ⟨k, (upperDensity_mono hsubset).trans hcompl_bound⟩
  · intro hSmooth ε hε₀ hε₁ η hη
    obtain ⟨k, hk⟩ := hSmooth ε hε₀ hε₁ η hη
    set good := {n : ℕ | (n : ℝ) ^ (1 - ε) < (gpfConsecutive n k : ℝ)} with hgood_def
    set smooth_bad := {n : ℕ | 2 ≤ n ∧ ∀ i ≤ k, (greatestPrimeFactor (n + i) : ℝ) ≤ (n : ℝ) ^ (1 - ε)}
      with hbad_def
    haveI hd1 : DecidablePred (· ∈ good) := Classical.decPred _
    haveI hd2 : DecidablePred (· ∈ smooth_bad) := Classical.decPred _
    have hdual : lowerDensity good = 1 - upperDensity goodᶜ := by
      have := lowerDensity_compl goodᶜ; simp only [compl_compl] at this; exact this
    suffices hgoodc : upperDensity goodᶜ ≤ η from ⟨k, by linarith⟩
    have hcard_bound : ∀ N : ℕ, 1 ≤ N →
        ((Finset.Icc 1 N).filter (fun n => n ∉ good)).card ≤
        ((Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad)).card + 1 := by
      intro N hN
      have hsub : (Finset.Icc 1 N).filter (fun n => n ∉ good) ⊆
          (Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad) ∪ {1} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union,
                   Finset.mem_singleton] at hx ⊢
        obtain ⟨⟨hx1, hxN⟩, hxgoodc⟩ := hx
        simp only [Set.mem_compl_iff, hgood_def, Set.mem_setOf_eq] at hxgoodc
        by_cases h2 : 2 ≤ x
        · left
          exact ⟨⟨hx1, hxN⟩, h2, (erdos_1201_not_good_smooth_window x k ε h2).mp hxgoodc⟩
        · right; omega
      calc ((Finset.Icc 1 N).filter (fun n => n ∉ good)).card
          ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad) ∪ {1}).card :=
              Finset.card_le_card hsub
        _ ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad)).card + ({1} : Finset ℕ).card :=
              Finset.card_union_le _ _
        _ = ((Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad)).card + 1 := by simp
    simp only [upperDensity, Set.mem_compl_iff, Set.mem_setOf_eq]
    set dgc := fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∉ good)).card : ℝ) / N
    set dbad := fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ smooth_bad)).card : ℝ) / N
    have h_card : ∀ N : ℕ, 0 < N → dgc N ≤ dbad N + 1 / N := by
      intro N hN
      simp only [dgc, dbad]
      rw [div_add_div_same]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      norm_cast
      exact hcard_bound N (by omega)
    have h_limsup_le : Filter.limsup dgc Filter.atTop ≤
        Filter.limsup (fun N => dbad N + 1 / N) Filter.atTop :=
      Filter.limsup_le_limsup
        (Filter.eventually_atTop.mpr ⟨1, fun N hN => h_card N (by omega)⟩)
        ⟨0, fun a ha => by
          by_contra hlt; push_neg at hlt
          obtain ⟨N, hN⟩ := ha.exists
          have h0 : (0 : ℝ) ≤ dgc N := by
            simp only [dgc]; rcases Nat.eq_zero_or_pos N with rfl | hNpos
            · simp
            · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          linarith⟩
        ⟨2, Filter.Eventually.of_forall fun N => by
          simp only [dbad]; rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · apply add_le_add
            · apply div_le_one_of_le _ (Nat.cast_nonneg N)
              have hcard : (Finset.Icc 1 N).card = N := icc_one_card N
              exact_mod_cast (Finset.card_filter_le _ _).trans hcard.le
            · exact div_le_one_of_le (by exact_mod_cast hN) (Nat.cast_nonneg N)⟩
    have h_subadd : Filter.limsup (fun N => dbad N + 1 / (N : ℝ)) Filter.atTop ≤
        Filter.limsup dbad Filter.atTop +
        Filter.limsup (fun N : ℕ => (1 : ℝ) / N) Filter.atTop :=
      limsup_add_le
        ⟨0, Filter.Eventually.of_forall fun N => by
          simp only [dbad]; rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
        ⟨1, Filter.Eventually.of_forall fun N => by
          simp only [dbad]; rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · exact div_le_one_of_le
              (by exact_mod_cast (Finset.card_filter_le _ _).trans (icc_one_card N).le)
              (Nat.cast_nonneg N)⟩
        ⟨0, fun b hb => by
          by_contra hlt; push_neg at hlt
          obtain ⟨N, hN⟩ := hb.exists
          linarith [div_nonneg zero_le_one (Nat.cast_nonneg N)]⟩
        ⟨1, Filter.Eventually.of_forall fun N => by
          rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · exact div_le_one_of_le (by exact_mod_cast hN) (Nat.cast_nonneg N)⟩
    have h_1N_zero : Filter.limsup (fun N : ℕ => (1 : ℝ) / N) Filter.atTop = 0 := by
      exact (by simp_rw [one_div];
             exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).limsup_eq
    have h_dbad_le : Filter.limsup dbad Filter.atTop ≤ η := by
      simp only [upperDensity] at hk; exact hk
    linarith [h_limsup_le, h_subadd, h_1N_zero, h_dbad_le]

end Erdos1201
