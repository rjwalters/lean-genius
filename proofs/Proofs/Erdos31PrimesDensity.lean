/-
Erdős Problem #31 Helper: Primes Have Density Zero

This file proves that the prime numbers have natural density zero,
establishing the proof architecture:

1. countingFn_primes_le_primeCounting: bridges our counting function with π(N)
2. chebyshevTheta_le: θ(N) ≤ N·log(4) (from primorial bound, proved)
3. primeCounting_le_chebyshev: π(N) ≤ 2N·log(4)/log(N) + √N + 1 (proved)
4. chebyshev_bound_tendsto_zero: the upper bound → 0 (proved)
5. primes_density_zero: the density result (proved)

Status: VERIFIED — 0 sorries, 0 axioms. Complete proof from Mathlib.
Dependencies: Only Mathlib (no other project files needed)
-/

import Mathlib

open Set Finset Nat Filter

namespace Erdos31PrimesDensity

/-! ## Density definitions -/

/-- The counting function |A ∩ {1,...,N}| for a set A ⊆ ℕ. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- A set A has density d if |A ∩ {1,...,N}| / N → d as N → ∞. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (countingFn A N : ℝ) / N) atTop (nhds d)

/-- A set has density 0. -/
def HasDensityZero (A : Set ℕ) : Prop := HasDensity A 0

/-! ## Bridging countingFn and primeCounting -/

/-- countingFn {n | n.Prime} N ≤ π(N).
    Primes in [1,N] ⊆ primes in {0,...,N} since 0 is not prime. -/
theorem countingFn_primes_le_primeCounting (N : ℕ) :
    countingFn {n : ℕ | n.Prime} N ≤ Nat.primeCounting N := by
  unfold countingFn Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro x hx
  simp only [Set.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc] at hx
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hx.1⟩

/-! ## Chebyshev theta bound -/

/-- The Chebyshev theta function: θ(n) = Σ_{p ≤ n, p prime} log(p) -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Real.log p

/-- θ(n) ≤ n · log(4), proved from the primorial bound n# ≤ 4^n. -/
theorem chebyshevTheta_le (n : ℕ) : chebyshevTheta n ≤ n * Real.log 4 := by
  unfold chebyshevTheta
  by_cases hn : n = 0
  · subst hn
    have : Finset.filter Nat.Prime (Finset.range 1) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty, iff_false, not_and]
      intro hx; interval_cases x; exact Nat.not_prime_zero
    simp [this]
  have hprim_pos : 0 < primorial n := primorial_pos n
  have hprim_real : (primorial n : ℝ) ≤ ((4 : ℕ) ^ n : ℕ) := by
    exact_mod_cast primorial_le_4_pow n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < primorial n) hprim_real
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  rw [Real.log_pow] at hlog
  have hprod_cast : (primorial n : ℝ) =
      ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (p : ℝ) := by
    unfold primorial; simp only [Nat.cast_prod]
  rw [hprod_cast] at hlog
  rw [Real.log_prod _ _ (fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero)] at hlog
  linarith

/-! ## Upper bound on π(N) from Chebyshev

**Strategy**: Split primes ≤ N into small (≤ √N) and large (> √N).
- Small primes: at most √N + 1
- Large primes p: each contributes log(p) ≥ log(√N) = (1/2)·log(N) to θ(N)
  So count of large primes ≤ θ(N)/log(√N) ≤ N·log(4)/((1/2)·log(N)) = 2N·log(4)/log(N)
- Total: π(N) ≤ (√N + 1) + 2N·log(4)/log(N)

This splitting argument is mathematically straightforward but requires careful
Lean formalization with Finset partitions. -/

/-- Upper bound on prime counting from Chebyshev:
    π(N) ≤ 2·N·log(4)/log(N) + √N + 1 for N ≥ 2.

    Proof: Split primes ≤ N at √N. Small primes (≤ √N): at most √N + 1.
    Large primes (> √N): each contributes ≥ (1/2)log(N) to θ(N) ≤ N·log(4),
    so their count ≤ 2N·log(4)/log(N). -/
theorem primeCounting_le_chebyshev (N : ℕ) (hN : 2 ≤ N) :
    (Nat.primeCounting N : ℝ) ≤ 2 * N * Real.log 4 / Real.log N + Nat.sqrt N + 1 := by
  set S := Finset.filter Nat.Prime (Finset.range (N + 1)) with hS_def
  set sqrtN := Nat.sqrt N with hsqrtN_def
  set S_small := S.filter (· ≤ sqrtN) with hS_small_def
  set S_large := S.filter (fun p => sqrtN < p) with hS_large_def
  have hS_union : S = S_small ∪ S_large := by
    ext p
    simp only [hS_small_def, hS_large_def, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p ≤ sqrtN
      · left; exact ⟨hp, h⟩
      · right; exact ⟨hp, by omega⟩
    · intro hp; rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩ <;> exact hp
  have hS_disj : Disjoint S_small S_large := by
    simp only [hS_small_def, hS_large_def, Finset.disjoint_filter]
    intro p _ h1 h2; omega
  have hpiN : Nat.primeCounting N = S.card := by
    simp only [hS_def, Nat.primeCounting, Nat.primeCounting']
    rw [Nat.count_eq_card_filter_range]
  have hcard_split : S.card = S_small.card + S_large.card := by
    rw [hS_union, Finset.card_union_of_disjoint hS_disj]
  have h_small_bound : (S_small.card : ℝ) ≤ Nat.sqrt N + 1 := by
    have hsub : S_small ⊆ Finset.range (sqrtN + 1) := by
      intro p hp
      simp only [hS_small_def, Finset.mem_filter] at hp
      simp only [Finset.mem_range]; omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    exact_mod_cast hcard
  have hlogN_pos : Real.log (N : ℝ) > 0 := by
    apply Real.log_pos; exact_mod_cast show 1 < N by omega
  have h_large_bound : (S_large.card : ℝ) ≤ 2 * N * Real.log 4 / Real.log N := by
    have h_log_lower : ∀ p ∈ S_large, Real.log (N : ℝ) / 2 ≤ Real.log (p : ℝ) := by
      intro p hp
      simp only [hS_large_def, Finset.mem_filter] at hp
      obtain ⟨hpS, hpgt⟩ := hp
      simp only [hS_def, Finset.mem_filter] at hpS
      have hp_sq_gt : N < p * p := by
        have hp_ge : sqrtN + 1 ≤ p := hpgt
        have h_succ_sq : N < (sqrtN + 1) * (sqrtN + 1) := by
          rw [hsqrtN_def]; exact Nat.lt_succ_sqrt' N
        nlinarith [Nat.mul_le_mul hp_ge hp_ge]
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpS.2.pos
      have hp_sq_real : (N : ℝ) < (p : ℝ) * (p : ℝ) := by exact_mod_cast hp_sq_gt
      rw [div_le_iff₀ (two_pos)]
      have hlog_mul : Real.log ((p : ℝ) * (p : ℝ)) = Real.log (p : ℝ) + Real.log (p : ℝ) :=
        Real.log_mul (ne_of_gt hp_pos) (ne_of_gt hp_pos)
      have hlog_lt : Real.log (N : ℝ) < Real.log ((p : ℝ) * (p : ℝ)) :=
        Real.log_lt_log (by exact_mod_cast (show 0 < N by omega)) hp_sq_real
      linarith
    have h_sum_lower : S_large.card * (Real.log N / 2) ≤
        ∑ p ∈ S_large, Real.log (p : ℝ) := by
      have := Finset.card_nsmul_le_sum S_large _ _ h_log_lower
      simp only [nsmul_eq_mul] at this; exact this
    have h_sum_le_theta : ∑ p ∈ S_large, Real.log (p : ℝ) ≤ chebyshevTheta N := by
      unfold chebyshevTheta
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [hS_large_def, Finset.mem_filter] at hp
        exact hp.1
      · intro p hp _
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
    have h_theta_bound := chebyshevTheta_le N
    have h_combined : S_large.card * (Real.log N / 2) ≤ N * Real.log 4 := by linarith
    rw [le_div_iff₀ hlogN_pos]
    nlinarith
  rw [hpiN, hcard_split, Nat.cast_add]
  linarith

/-! ## Tendsto results -/

/-- The Chebyshev-derived upper bound tends to zero. -/
theorem chebyshev_bound_tendsto_zero :
    Tendsto (fun N : ℕ => 2 * Real.log 4 / Real.log N + (Nat.sqrt N + 1 : ℝ) / N)
      atTop (nhds 0) := by
  -- 2·log(4)/log(N) → 0
  have h1 : Tendsto (fun N : ℕ => 2 * Real.log 4 / Real.log (N : ℝ)) atTop (nhds 0) := by
    have hlog_nat : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp hlog_nat
    have := hinv.const_mul (2 * Real.log 4)
    simp only [mul_zero] at this
    exact this.congr' (by filter_upwards with N; ring)
  -- (√N + 1)/N → 0
  have h2 : Tendsto (fun N : ℕ => (Nat.sqrt N + 1 : ℝ) / N) atTop (nhds 0) := by
    have h_upper : Tendsto (fun N : ℕ => (2 : ℝ) / Real.sqrt N) atTop (nhds 0) := by
      have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
        have := (tendsto_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num)).comp
          tendsto_natCast_atTop_atTop
        exact this.congr' (by filter_upwards [eventually_ge_atTop 0] with N _; simp [Real.sqrt_eq_rpow])
      have := (tendsto_inv_atTop_zero.comp hsqrt).const_mul 2
      simp only [mul_zero] at this
      exact this.congr' (by filter_upwards with N; ring)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 4] with N hN
      have hN_pos : (0 : ℝ) < N := by positivity
      have hN_sqrt_pos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
      rw [div_le_div_iff₀ hN_pos hN_sqrt_pos]
      have hsqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt N))]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' N)
      have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (le_of_lt hN_pos)
      -- Need: (Nat.sqrt N + 1) * √N ≤ 2 * N
      -- (√N + 1) * √N = √N² + √N = N + √N ≤ 2N since √N ≤ N
      nlinarith [sq_nonneg (Real.sqrt N - 1)]
  have := h1.add h2
  simp only [zero_add] at this
  exact this

/-! ## Main result -/

/-- **Primes have density zero**: |{p prime : p ≤ N}| / N → 0 as N → ∞.

    This follows from:
    1. countingFn for primes ≤ π(N) (countingFn_primes_le_primeCounting)
    2. π(N) ≤ 2N·log(4)/log(N) + √N + 1 (primeCounting_le_chebyshev, from Chebyshev)
    3. The upper bound → 0 (chebyshev_bound_tendsto_zero) -/
theorem primes_density_zero : HasDensityZero {n : ℕ | n.Prime} := by
  unfold HasDensityZero HasDensity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds chebyshev_bound_tendsto_zero
  · filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN_pos : (0 : ℝ) < N := by positivity
    have h1 : (countingFn {n : ℕ | n.Prime} N : ℝ) ≤ Nat.primeCounting N :=
      Nat.cast_le.mpr (countingFn_primes_le_primeCounting N)
    have h2 : (Nat.primeCounting N : ℝ) ≤ 2 * N * Real.log 4 / Real.log N + Nat.sqrt N + 1 :=
      primeCounting_le_chebyshev N hN
    calc (countingFn {n : ℕ | n.Prime} N : ℝ) / N
        ≤ (2 * N * Real.log 4 / Real.log N + Nat.sqrt N + 1) / N := by
          exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hN_pos)
      _ = 2 * Real.log 4 / Real.log N + (Nat.sqrt N + 1) / N := by
          field_simp; ring

end Erdos31PrimesDensity
