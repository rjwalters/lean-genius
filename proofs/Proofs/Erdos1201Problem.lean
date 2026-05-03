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
  Filter.limsup (fun N : ℕ =>
    ((Finset.Icc 1 N).filter (fun n => n ∈ S)).card / (N : ℝ))
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
  have h : n.primeFactors.Nonempty := Nat.primeFactors_nonempty.mpr (by omega)
  rw [dif_pos h]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ h)

/-- greatestPrimeFactor n ∈ n.primeFactors when n ≥ 2. -/
theorem gpf_mem_primeFactors (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∈ n.primeFactors := by
  unfold greatestPrimeFactor
  have h : n.primeFactors.Nonempty := Nat.primeFactors_nonempty.mpr (by omega)
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

/-- consecutiveProduct n k is positive when n ≥ 1. -/
theorem consecutiveProduct_pos (n k : ℕ) (hn : 1 ≤ n) : 0 < consecutiveProduct n k := by
  apply Finset.prod_pos
  intro i _
  omega

/-- n divides consecutiveProduct n k. -/
theorem dvd_consecutiveProduct_left (n k : ℕ) : n ∣ consecutiveProduct n k := by
  apply Finset.dvd_prod_of_mem
  simp [Finset.mem_range]

/-- (n+k) divides consecutiveProduct n k. -/
theorem dvd_consecutiveProduct_right (n k : ℕ) : n + k ∣ consecutiveProduct n k := by
  apply Finset.dvd_prod_of_mem
  simp [consecutiveProduct, Finset.mem_range]

/-- consecutiveProduct n k = n * consecutiveProduct (n+1) (k-1) for k ≥ 1. -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = n * consecutiveProduct (n + 1) k := by
  unfold consecutiveProduct
  rw [Finset.range_succ', Finset.prod_insert (by simp)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

/-
## Monotonicity of gpfConsecutive in k
-/

/-- If p divides consecutiveProduct n k, it divides consecutiveProduct n (k+1). -/
theorem dvd_consecutiveProduct_of_dvd_lt (n k : ℕ) (p : ℕ) (hp : p ∣ consecutiveProduct n k) :
    p ∣ consecutiveProduct n (k + 1) := by
  unfold consecutiveProduct at *
  apply Dvd.dvd.trans hp
  apply Finset.prod_dvd_prod_of_subset
  simp [Finset.range_subset]

/-- gpfConsecutive is monotone in k: increasing k can only increase or maintain the gpf. -/
theorem gpfConsecutive_mono (n k : ℕ) (hn : 2 ≤ n) :
    gpfConsecutive n k ≤ gpfConsecutive n (k + 1) := by
  unfold gpfConsecutive greatestPrimeFactor
  have h1 : (consecutiveProduct n k).primeFactors.Nonempty := by
    apply Nat.primeFactors_nonempty.mpr
    have := consecutiveProduct_pos n k (by omega)
    omega
  rw [dif_pos h1]
  have h2 : (consecutiveProduct n (k + 1)).primeFactors.Nonempty := by
    apply Nat.primeFactors_nonempty.mpr
    have := consecutiveProduct_pos n (k + 1) (by omega)
    omega
  rw [dif_pos h2]
  apply Finset.max'_le _ _ _ h2
  intro p hp
  apply Finset.le_max'
  -- p ∈ (consecutiveProduct n (k+1)).primeFactors
  -- from p ∈ (consecutiveProduct n k).primeFactors
  rw [Nat.mem_primeFactors] at hp ⊢
  obtain ⟨hpp, hpdvd, hne⟩ := hp
  refine ⟨hpp, ?_, by
    have := consecutiveProduct_pos n (k + 1) (by omega); omega⟩
  exact dvd_consecutiveProduct_of_dvd_lt n k p hpdvd

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
    apply dvd_trans hpi
    apply Finset.dvd_prod_of_mem
    simp [consecutiveProduct, Finset.mem_range]
    omega
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
        apply Finset.prod_le_prod_of_subset
        · exact Finset.range_mono (by omega)
        · intro i _
          exact le_refl _

/-- gpfConsecutive n k ≥ 2 when n ≥ 2. -/
theorem gpfConsecutive_ge_two (n k : ℕ) (hn : 2 ≤ n) : 2 ≤ gpfConsecutive n k := by
  unfold gpfConsecutive
  apply gpf_ge_two
  calc 2 ≤ n := hn
    _ ≤ consecutiveProduct n k := consecutiveProduct_ge_n n k (by omega)

/-
## Comparison with ε = 1/2 case
-/

/-- The ε = 1/2 condition: P(n, k) > √n is equivalent to P(n,k)² > n when P(n,k) ≥ 1. -/
theorem gpfConsecutive_half_iff (n k : ℕ) (hn : 2 ≤ n) :
    Real.sqrt n < (gpfConsecutive n k : ℝ) ↔
    n < (gpfConsecutive n k) ^ 2 := by
  rw [← Real.sqrt_lt' (by positivity)]
  simp [Real.sqrt_lt_sqrt_iff (by positivity)]

/-- The ε = 1/2 partial result specializes to: ∀ η > 0, ∃ k, density of
    {n | gpfConsecutive n k² > n} ≥ 1 - η. -/
theorem erdos_1201_half_squared (η : ℝ) (hη : 0 < η) :
    ∃ k : ℕ,
      upperDensity {n : ℕ | n < (gpfConsecutive n k) ^ 2} ≥ 1 - η := by
  obtain ⟨k, hk⟩ := erdos_1201_half_case η hη
  refine ⟨k, ?_⟩
  have : {n : ℕ | Real.sqrt n < (gpfConsecutive n k : ℝ)} =
         {n : ℕ | n < (gpfConsecutive n k) ^ 2} := by
    ext n
    constructor
    · intro h
      have hn2 : 2 ≤ n := by
        by_contra hlt
        push_neg at hlt
        interval_cases n <;> simp [gpfConsecutive, consecutiveProduct, greatestPrimeFactor] at h ⊢
      rwa [gpfConsecutive_half_iff n k hn2] at h
    · intro h
      have hn2 : 2 ≤ n := by
        by_contra hlt
        push_neg at hlt
        interval_cases n <;> simp [gpfConsecutive, consecutiveProduct, greatestPrimeFactor] at h ⊢
      rwa [← gpfConsecutive_half_iff n k hn2]
  rwa [this] at hk

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
  apply Finset.dvd_prod_of_mem
  simp [Finset.mem_range]
  omega

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
  apply Finset.max'_le _ _ h
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

end Erdos1201
