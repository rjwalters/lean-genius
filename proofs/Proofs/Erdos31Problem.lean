/-
Erdős Problem #31: Additive Complements

Source: https://erdosproblems.com/31
Status: SOLVED (Lorentz 1954)

Statement:
Given any infinite set A ⊂ ℕ, there exists a set B of density 0 such that
A + B contains all except finitely many positive integers.

History:
- Erdős-Straus: Conjectured this result
- Lorentz (1954): Proved the conjecture [Lo54]

The result shows that any infinite set can be "completed" to cover almost all
of ℕ using only a very sparse set B. This is a fundamental result in additive
combinatorics about the complementary structure of sets.

Reference: Lorentz, G.G. "On a problem of additive number theory" (1954)
-/

import Mathlib

open Set Finset Nat Filter

namespace Erdos31

/- ## Density Definitions -/

/-- The counting function |A ∩ {1,...,N}| for a set A ⊆ ℕ. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- A set A has density d if |A ∩ {1,...,N}| / N → d as N → ∞. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (countingFn A N : ℝ) / N) atTop (nhds d)

/-- A set has density 0. -/
def HasDensityZero (A : Set ℕ) : Prop := HasDensity A 0

/-- Upper density of a set. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => (countingFn A N : ℝ) / N) atTop

/-- A set has upper density 0 if its upper density is 0. -/
def HasUpperDensityZero (A : Set ℕ) : Prop := upperDensity A = 0

/- ## Sumsets -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def Sumset (A B : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

notation:65 A " +ₛ " B => Sumset A B

/-- A + B contains all sufficiently large integers (covers a cofinite set). -/
def CoversCofinite (A B : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ (A +ₛ B)

/-- A + B contains all except finitely many positive integers. -/
def CoversAllButFinitely (A B : Set ℕ) : Prop :=
  (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}).Finite

/- ## Primes Have Density Zero (Chebyshev Bound)

The proof uses the Chebyshev theta bound θ(n) ≤ n·log(4) from the primorial
bound n# ≤ 4^n, then splits primes into small (≤ √N) and large (> √N). -/

/-- countingFn {n | n.Prime} N ≤ π(N). -/
theorem countingFn_primes_le_primeCounting (N : ℕ) :
    countingFn {n : ℕ | n.Prime} N ≤ Nat.primeCounting N := by
  unfold countingFn Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro x hx
  simp only [Set.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc] at hx
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hx.1⟩

/-- The Chebyshev theta function: θ(n) = Σ_{p ≤ n, p prime} log(p) -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Real.log p

/-- θ(n) ≤ n · log(4), proved from the primorial bound n# ≤ 4^n. -/
theorem chebyshevTheta_le (n : ℕ) : chebyshevTheta n ≤ n * Real.log 4 := by
  unfold chebyshevTheta
  by_cases hn : n = 0
  · subst hn
    have hempty : Finset.filter Nat.Prime (Finset.range 1) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hx
      exact fun hp => absurd (hp.one_le) (by omega)
    simp [hempty]
  · have hprim_pos : 0 < primorial n := primorial_pos n
    have hprim_real : (primorial n : ℝ) ≤ ((4 : ℕ) ^ n : ℕ) := by
      exact_mod_cast primorial_le_4_pow n
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < primorial n) hprim_real
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hlog
    rw [Real.log_pow] at hlog
    have hprod_cast : (primorial n : ℝ) =
        ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (p : ℝ) := by
      unfold primorial; simp only [Nat.cast_prod]
    rw [hprod_cast] at hlog
    have hne_zero : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
        (p : ℝ) ≠ 0 := by
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    rw [Real.log_prod _ _ hne_zero] at hlog
    linarith

/-- Upper bound on prime counting from Chebyshev:
    π(N) ≤ 2·N·log(4)/log(N) + √N + 1 for N ≥ 2. -/
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

/-- The Chebyshev-derived upper bound tends to zero. -/
theorem chebyshev_bound_tendsto_zero :
    Tendsto (fun N : ℕ => 2 * Real.log 4 / Real.log N + (Nat.sqrt N + 1 : ℝ) / N)
      atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => 2 * Real.log 4 / Real.log (N : ℝ)) atTop (nhds 0) := by
    have hlog_nat : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp hlog_nat
    have := hinv.const_mul (2 * Real.log 4)
    simp only [mul_zero] at this
    exact this.congr' (by filter_upwards with N; ring)
  have h2 : Tendsto (fun N : ℕ => (Nat.sqrt N + 1 : ℝ) / N) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (nhds 0) from by
        have : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        have h2 := this.const_mul 2
        simp only [mul_zero] at h2
        exact h2.congr' (by filter_upwards with N; rw [div_eq_mul_inv]))
    · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 4] with N hN
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ N)
      have hsqrt_le : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
      exact_mod_cast show Nat.sqrt N + 1 ≤ 2 * N by omega
  have := h1.add h2
  simp only [zero_add] at this
  exact this

/-- The primes form an infinite set of density 0.

Proved from the Chebyshev theta bound θ(n) ≤ n·log(4), which comes from
the primorial bound n# ≤ 4^n. The key splitting argument partitions primes
at √N: small primes contribute at most √N+1, large primes are bounded by
the theta function. -/
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

/- ## Properties of Sparse Sets -/

/-- Bijection between powers of 2 in [1,N] and {0,...,log₂ N}.
    The powers of 2 in [1,N] are exactly {2^0, 2^1, ..., 2^k} where k = ⌊log₂ N⌋. -/
lemma powers_of_2_in_Icc_eq (N : ℕ) (hN : N ≥ 1) :
    {n : ℕ | ∃ k, n = 2^k} ∩ Set.Icc 1 N = (Set.Icc 0 (Nat.log 2 N)).image (2 ^ ·) := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_image]
  constructor
  · rintro ⟨⟨k, rfl⟩, h1, h2⟩
    use k
    constructor
    · constructor
      · omega
      · rw [← Nat.log_pow (by norm_num : 1 < 2) k]
        exact Nat.log_mono_right h2
    · rfl
  · rintro ⟨k, ⟨_, hklog⟩, rfl⟩
    constructor
    · exact ⟨k, rfl⟩
    · constructor
      · exact Nat.one_le_pow k 2 (by norm_num)
      · calc 2^k ≤ 2^(Nat.log 2 N) := Nat.pow_le_pow_right (by norm_num) hklog
          _ ≤ N := Nat.pow_log_le_self 2 (by omega)

/-- The number of powers of 2 up to N is at most log₂(N) + 1.
    This is because 2^k ≤ N iff k ≤ log₂(N), so the set is {2^0, ..., 2^(log₂ N)}. -/
theorem powers_of_2_count_bound (N : ℕ) :
    ({n : ℕ | ∃ k, n = 2^k} ∩ Set.Icc 1 N).ncard ≤ Nat.log 2 N + 1 := by
  by_cases hN : N = 0
  · -- N = 0: Icc 1 0 is empty, so intersection is empty
    subst hN
    have h : Set.Icc 1 0 = (∅ : Set ℕ) := by
      ext x; simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false]; omega
    simp only [h, Set.inter_empty, Set.ncard_empty, Nat.log_zero_right, zero_add]
    decide
  · -- N ≥ 1: use the bijection
    have hN1 : N ≥ 1 := Nat.one_le_iff_ne_zero.mpr hN
    rw [powers_of_2_in_Icc_eq N hN1]
    have hfin : (Set.Icc 0 (Nat.log 2 N)).Finite := Set.finite_Icc 0 (Nat.log 2 N)
    calc Set.ncard ((Set.Icc 0 (Nat.log 2 N)).image (2 ^ ·))
        ≤ Set.ncard (Set.Icc 0 (Nat.log 2 N)) := Set.ncard_image_le hfin
      _ = Nat.log 2 N + 1 := by
          rw [Set.ncard_eq_toFinset_card']
          simp only [Set.toFinset_Icc, Nat.card_Icc]
          omega

/-- (log N + 1) / N → 0 as N → ∞.

**Proof**: We use the squeeze theorem. Since Nat.log 2 N ≤ Real.log N / Real.log 2,
we have (Nat.log 2 N + 1) / N ≤ (Real.log N / Real.log 2 + 1) / N → 0.
-/
theorem tendsto_log_add_one_div : Filter.Tendsto (fun N : ℕ => (Nat.log 2 N + 1 : ℝ) / N)
    Filter.atTop (nhds 0) := by
  -- Use squeeze: 0 ≤ f(N) ≤ (log N / log 2 + 1) / N → 0
  have h_upper : Filter.Tendsto (fun N : ℕ => (Real.log N / Real.log 2 + 1) / N)
      Filter.atTop (nhds 0) := by
    -- log N / N → 0 from tendsto_pow_log_div_mul_add_atTop
    have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Filter.Tendsto (fun N : ℕ => Real.log N / N) Filter.atTop (nhds 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    -- (log N / log 2) / N = (log N / N) / log 2 → 0 / log 2 = 0
    have h3 : Filter.Tendsto (fun N : ℕ => Real.log N / Real.log 2 / N) Filter.atTop (nhds 0) := by
      have hlog2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      have := h2.div_const (Real.log 2)
      simp only [zero_div] at this
      refine this.congr' ?_
      filter_upwards with N
      ring
    -- 1/N → 0
    have h4 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / N) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    -- Sum of limits
    have h5 := h3.add h4
    simp only [zero_add] at h5
    refine h5.congr' ?_
    filter_upwards with N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ N)
    have hN_pos : (1 : ℝ) < N := Nat.one_lt_cast.mpr hN
    have hN_pos' : (0 : ℝ) < N := by linarith
    -- Nat.log 2 N ≤ Real.log N / Real.log 2
    -- Using: 2^(Nat.log 2 N) ≤ N, so (Nat.log 2 N) * log 2 = log(2^(Nat.log 2 N)) ≤ log N
    have h_log_bound : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
      have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      rw [le_div_iff₀ hlog2_pos]
      by_cases hN1 : N = 1
      · simp [hN1, Real.log_one]
      · have hN2 : N ≠ 0 := by omega
        -- 2^(Nat.log 2 N) ≤ N
        have hpow := Nat.pow_log_le_self 2 hN2
        have hpow' : (((2 : ℕ) ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hpow
        calc (Nat.log 2 N : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ Nat.log 2 N) := by rw [Real.log_pow]
            _ = Real.log (((2 : ℕ) ^ Nat.log 2 N : ℕ) : ℝ) := by
                congr 1
                simp only [Nat.cast_pow, Nat.cast_ofNat]
            _ ≤ Real.log (N : ℝ) := by
              apply Real.log_le_log
              · have : (1 : ℕ) ≤ 2 ^ Nat.log 2 N := Nat.one_le_pow _ _ (by norm_num)
                exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one this)
              · exact hpow'
    linarith

/-- The powers of 2 form a set of density 0. -/
theorem powers_of_2_density_zero : HasDensityZero {n : ℕ | ∃ k : ℕ, n = 2^k} := by
  unfold HasDensityZero HasDensity countingFn
  -- Key: |{2^k : 2^k ≤ N}| ≤ log₂(N) + 1, so ratio ≤ (log₂(N) + 1)/N → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_log_add_one_div
  · filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN_pos : (0 : ℝ) ≤ (N : ℝ) := le_of_lt (Nat.cast_pos.mpr hN)
    apply div_le_div_of_nonneg_right _ hN_pos
    exact_mod_cast powers_of_2_count_bound N

/-- Bijection between squares in [1,N] and {1,...,√N}.
    The squares in [1,N] are exactly {1², 2², ..., k²} where k = ⌊√N⌋. -/
lemma squares_in_Icc_eq (N : ℕ) (_hN : N ≥ 1) :
    {n : ℕ | ∃ k, n = k^2} ∩ Set.Icc 1 N = (Set.Icc 1 (Nat.sqrt N)).image (·^2) := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_image]
  constructor
  · rintro ⟨⟨k, rfl⟩, h1, h2⟩
    use k
    constructor
    · constructor
      · -- k ≥ 1 from k² ≥ 1
        by_contra hk
        push_neg at hk
        interval_cases k; omega
      · -- k ≤ √N from k² ≤ N
        rw [Nat.le_sqrt]
        simp only [pow_two] at h2
        exact h2
    · rfl
  · rintro ⟨k, ⟨hk1, hksqrt⟩, rfl⟩
    constructor
    · exact ⟨k, rfl⟩
    · constructor
      · nlinarith
      · -- k² ≤ N from k ≤ √N
        have hsqrt : k ≤ Nat.sqrt N := hksqrt
        calc k^2 = k * k := by ring
          _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul hsqrt hsqrt
          _ ≤ N := Nat.sqrt_le N

/-- The number of perfect squares up to N is at most √N + 1.
    This is because k² ≤ N iff k ≤ √N, so the squares are {1², 2², ..., (√N)²}. -/
theorem squares_count_bound (N : ℕ) :
    ({n : ℕ | ∃ k, n = k^2} ∩ Set.Icc 1 N).ncard ≤ Nat.sqrt N + 1 := by
  by_cases hN : N = 0
  · subst hN
    have h : Set.Icc 1 0 = (∅ : Set ℕ) := by
      ext x; simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false]; omega
    simp only [h, Set.inter_empty, Set.ncard_empty, Nat.sqrt_zero, zero_add]
    norm_num
  · have hN1 : N ≥ 1 := Nat.one_le_iff_ne_zero.mpr hN
    rw [squares_in_Icc_eq N hN1]
    have hfin : (Set.Icc 1 (Nat.sqrt N)).Finite := Set.finite_Icc 1 (Nat.sqrt N)
    calc Set.ncard ((Set.Icc 1 (Nat.sqrt N)).image (·^2))
        ≤ Set.ncard (Set.Icc 1 (Nat.sqrt N)) := Set.ncard_image_le hfin
      _ = Nat.sqrt N := by
          rw [Set.ncard_eq_toFinset_card']
          simp only [Set.toFinset_Icc, Nat.card_Icc]
          omega
      _ ≤ Nat.sqrt N + 1 := by omega

/-- (√N + 1)/N → 0 as N → ∞.

**Proof**: We use √N ≤ N, so (√N + 1)/N ≤ 2√N/N = 2/√N → 0.
-/
theorem tendsto_sqrt_inv : Filter.Tendsto (fun N : ℕ => (Nat.sqrt N + 1 : ℝ) / N)
    Filter.atTop (nhds 0) := by
  -- Use squeeze: 0 ≤ (√N + 1)/N ≤ 2/√N → 0 for N ≥ 1
  have h_upper : Filter.Tendsto (fun N : ℕ => (2 : ℝ) / Real.sqrt N) Filter.atTop (nhds 0) := by
    -- sqrt N = N^(1/2), and x^(1/2) → ∞ as x → ∞ (since 1/2 > 0)
    have h1 : Filter.Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) Filter.atTop Filter.atTop := by
      have hsqrt : Filter.Tendsto (fun x : ℝ => x ^ (1/2 : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)
      have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      have := hsqrt.comp hcast
      refine this.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 0] with N _
      simp only [Function.comp_apply, Real.sqrt_eq_rpow]
    have h2 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / Real.sqrt N) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul 2
    simp only [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards with N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    have hN_pos' : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
    -- (√N + 1)/N ≤ 2/√N  iff  (√N + 1) * √N ≤ 2N  iff  N + √N ≤ 2N  iff  √N ≤ N
    rw [div_le_div_iff₀ hN_pos hN_pos']
    have hsqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
      have h1 : (Nat.sqrt N : ℝ) ^ 2 = ((Nat.sqrt N)^2 : ℕ) := by simp
      have h2 : ((Nat.sqrt N)^2 : ℕ) ≤ N := by
        exact Nat.sqrt_le' N
      have h3 : (Nat.sqrt N : ℝ) ^ 2 ≤ N := by
        rw [h1]
        exact Nat.cast_le.mpr h2
      rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt h3
    have hsqrt_le_N : Real.sqrt N ≤ N := by
      have h1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
      have hN_sq : (N : ℝ) ≤ N ^ 2 := by
        have : (1 : ℝ) ≤ N := h1
        nlinarith
      calc Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hN_sq
        _ = N := Real.sqrt_sq (le_of_lt hN_pos)
    calc (Nat.sqrt N + 1 : ℝ) * Real.sqrt N
        ≤ (Real.sqrt N + 1) * Real.sqrt N := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact le_of_lt hN_pos'
        _ = Real.sqrt N ^ 2 + Real.sqrt N := by ring
        _ = N + Real.sqrt N := by rw [Real.sq_sqrt (le_of_lt hN_pos)]
        _ ≤ N + N := by linarith
        _ = 2 * N := by ring

/-- Squares form a set of density 0. -/
theorem squares_density_zero : HasDensityZero {n : ℕ | ∃ k : ℕ, n = k^2} := by
  unfold HasDensityZero HasDensity countingFn
  -- Key: |{k² : k² ≤ N}| ≤ √N + 1, so ratio ≤ (√N + 1)/N → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_sqrt_inv
  · filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN_pos : (0 : ℝ) ≤ (N : ℝ) := le_of_lt (Nat.cast_pos.mpr hN)
    apply div_le_div_of_nonneg_right _ hN_pos
    exact_mod_cast squares_count_bound N

/- ## The Main Theorem -/

/--
**Erdős Problem #31** (SOLVED - Lorentz 1954):
For any infinite set A ⊆ ℕ, there exists a set B of density 0 such that
A + B covers all but finitely many positive integers.
-/
def Erdos31Statement : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely A B

/-- Cofinite coverage implies all-but-finitely coverage: if A + B covers
    all n ≥ N₀, then the uncovered positive integers form a finite set
    (subset of {0, ..., N₀ - 1}). -/
theorem coversCofinite_implies_allButFinitely (A B : Set ℕ)
    (h : CoversCofinite A B) : CoversAllButFinitely A B := by
  obtain ⟨N₀, hN₀⟩ := h
  unfold CoversAllButFinitely
  apply Set.Finite.subset (Finset.range N₀).finite_toSet
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, true_and,
             Set.mem_setOf_eq] at hn
  by_contra h_ge
  push_neg at h_ge
  exact hn.1 (hN₀ n h_ge)

/-- Any finite set has density zero: |B ∩ [1,N]|/N → 0 since the numerator
    is bounded by |B| while the denominator → ∞. -/
theorem finite_has_density_zero (B : Set ℕ) (hB : B.Finite) : HasDensityZero B := by
  unfold HasDensityZero HasDensity
  -- countingFn B N ≤ B.ncard for all N (intersection ⊆ whole set)
  have hbound : ∀ N, (countingFn B N : ℝ) ≤ B.ncard := fun N =>
    Nat.cast_le.mpr (Set.ncard_le_ncard Set.inter_subset_left hB)
  -- B.ncard / N → 0 (constant / N → 0)
  have h_upper : Tendsto (fun N : ℕ => (B.ncard : ℝ) / N) atTop (nhds 0) := by
    have h_inv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := h_inv.const_mul (B.ncard : ℝ)
    simp only [mul_zero] at this
    exact this.congr' (by filter_upwards with N; simp [div_eq_mul_inv, mul_comm])
  -- Squeeze: 0 ≤ countingFn B N / N ≤ B.ncard / N, both bounds → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (by filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (by filter_upwards with N
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp [div_zero]
        · exact (div_le_div_right (Nat.cast_pos.mpr hN)).mpr (hbound N))

/-- **Erdős #31 for bounded gaps**: If every integer ≥ a₀ is within distance M
    of some element of A, then B = {0, ..., M-1} gives density 0 and full coverage.

    This proves the special case without Lorentz's full construction. Sets with
    bounded gaps include arithmetic progressions and finite unions thereof.

    **Proof**: B = {0,...,M-1} is finite (density 0). For any n ≥ a₀, there exists
    a ∈ A with a ≤ n and n - a < M, so n = a + (n-a) ∈ A + B. -/
theorem erdos31_bounded_gaps (A : Set ℕ) (M : ℕ) (hM : 0 < M)
    (a₀ : ℕ) (ha₀ : a₀ ∈ A)
    (hgap : ∀ n ≥ a₀, ∃ a ∈ A, a ≤ n ∧ n < a + M) :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely A B := by
  refine ⟨Set.Iio M, ?_, ?_⟩
  · -- {0,...,M-1} is finite, hence has density 0
    exact finite_has_density_zero _ (Set.Finite.subset (Finset.range M).finite_toSet
      (fun x hx => Finset.mem_range.mpr (Set.mem_Iio.mp hx)))
  · -- A + {0,...,M-1} covers all n ≥ a₀
    apply coversCofinite_implies_allButFinitely
    exact ⟨a₀, fun n hn => by
      obtain ⟨a, haA, hle, hlt⟩ := hgap n hn
      exact ⟨a, haA, n - a, Set.mem_Iio.mpr (by omega), by omega⟩⟩

/- ## Axiom-Free Special Cases via Bounded Gaps

The following instances of Erdős #31 hold unconditionally — they are
direct applications of `erdos31_bounded_gaps` and do not depend on
`lorentz_theorem`. They cover the families of sets whose gaps are
bounded (multiples of any positive `k`, in particular the even
numbers).
-/

/-- Multiples of any positive `k` have bounded gaps (= `k`), so
    `erdos31_bounded_gaps` yields the finite density-0 completion
    `B = {0, 1, ..., k-1}`. Axiom-free instance of Erdős Problem #31.

    **Proof**: For every `n`, the multiple `k * (n / k)` lies in `[n - k + 1, n]`
    (using `k * (n / k) ≤ n` from `Nat.div_mul_le_self` and
    `n < k * (n / k) + k` from `Nat.div_add_mod` together with `n % k < k`).
    Then apply `erdos31_bounded_gaps` with `M = k`. -/
theorem multiples_have_sparse_complement (k : ℕ) (hk : 0 < k) :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely {n : ℕ | k ∣ n} B := by
  refine erdos31_bounded_gaps {n : ℕ | k ∣ n} k hk 0 (dvd_zero k) ?_
  intro n _
  refine ⟨k * (n / k), dvd_mul_right k _, ?_, ?_⟩
  · calc k * (n / k) = n / k * k := by ring
      _ ≤ n := Nat.div_mul_le_self n k
  · have hmod : n % k < k := Nat.mod_lt n hk
    have hdm : k * (n / k) + n % k = n := Nat.div_add_mod n k
    linarith

/-- Even numbers have the finite density-0 completion `B = {0, 1}`.
    Direct corollary of `multiples_have_sparse_complement` with `k = 2`. -/
theorem even_numbers_have_sparse_complement :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely {n : ℕ | 2 ∣ n} B :=
  multiples_have_sparse_complement 2 (by norm_num)

/-- The Lorentz theorem affirms Erdős Problem #31. -/
axiom lorentz_theorem : Erdos31Statement

/- ## Lorentz's Construction

The proof constructs B as follows:
1. Enumerate A = {a₁ < a₂ < a₃ < ...}
2. For each aᵢ, include in B certain "gaps" that need filling
3. The sparseness of A (infinite but thin) allows B to be chosen sparse

Key insight: If A is very sparse, B can be dense (worst case).
If A is dense, B can be very sparse. The balance works out.
-/

/- ## Special Cases -/

/-- For A = {2^k : k ∈ ℕ}, Lorentz's theorem gives us a sparse B. -/
example : ∃ B : Set ℕ, HasDensityZero B ∧
    CoversAllButFinitely {n : ℕ | ∃ k : ℕ, n = 2^k} B := by
  -- Apply Lorentz's theorem to the infinite set of powers of 2
  have hA_inf : {n : ℕ | ∃ k : ℕ, n = 2^k}.Infinite := by
    have : Set.range (fun k : ℕ => 2^k) = {n : ℕ | ∃ k : ℕ, n = 2^k} := by
      ext n
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor <;> (intro ⟨k, hk⟩; exact ⟨k, hk.symm⟩)
    rw [← this]
    apply Set.infinite_range_of_injective
    exact Nat.pow_right_injective (by norm_num : 1 < 2)
  exact lorentz_theorem _ hA_inf

/-- For A = primes, Lorentz's construction gives a very sparse B.

**Proof**: Apply Lorentz's theorem to the primes, which are infinite
by Euclid's theorem (`Nat.infinite_setOf_prime`). -/
theorem primes_have_sparse_complement :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely {n : ℕ | n.Prime} B :=
  lorentz_theorem _ Nat.infinite_setOf_prime

/- ## Density Properties -/

/-- The optimal density bound depends on the structure of A. -/
noncomputable def OptimalBDensity (A : Set ℕ) : ℝ :=
  sInf { d : ℝ | ∃ B : Set ℕ, HasDensity B d ∧ CoversAllButFinitely A B }

/-- Density is always non-negative (technical lemma).

**Proof**: Density is the limit of ratios |B ∩ [1,N]| / N, which are all non-negative.
The limit of non-negative values is non-negative. -/
theorem density_nonneg (B : Set ℕ) (d : ℝ) (hd : HasDensity B d) : d ≥ 0 := by
  unfold HasDensity at hd
  -- The ratio countingFn B N / N is always ≥ 0
  have h_nonneg : ∀ N : ℕ, (countingFn B N : ℝ) / N ≥ 0 := fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- Use ge_of_tendsto: limit of f(n) ≥ 0 when f(n) ≥ 0 for all n
  exact ge_of_tendsto hd (univ_mem' h_nonneg)

/-- For any infinite A, the optimal B-density is 0. -/
theorem optimal_B_density_zero (A : Set ℕ) (hA : A.Infinite) :
    OptimalBDensity A = 0 := by
  -- This follows from Lorentz's theorem: there exists B with density 0
  unfold OptimalBDensity
  -- The set contains 0 (from Lorentz), and 0 is the minimum possible density
  apply le_antisymm
  · -- sInf ≤ 0: because 0 is in the set
    apply csInf_le
    · -- The set is bounded below by 0 (densities are ≥ 0)
      use 0
      intro d ⟨B, hdens, _⟩
      exact density_nonneg B d hdens
    · -- 0 is in the set: Lorentz gives us B with HasDensity B 0
      obtain ⟨B, hB, hcover⟩ := lorentz_theorem A hA
      exact ⟨B, hB, hcover⟩
  · -- 0 ≤ sInf: infimum of set of densities is ≥ 0
    apply le_csInf
    · -- Nonempty: from Lorentz
      obtain ⟨B, hB, hcover⟩ := lorentz_theorem A hA
      exact ⟨0, B, hB, hcover⟩
    · -- Every element is ≥ 0
      intro d ⟨B, hdens, _⟩
      exact density_nonneg B d hdens

/- ## Converse Direction -/

/-- Question: If A + B covers almost all of ℕ, how dense must A ∪ B be?
    Answer: At least positive density is needed (obvious). -/

theorem coverage_requires_density (A B : Set ℕ) :
    CoversAllButFinitely A B → ¬(HasDensityZero A ∧ HasDensityZero B) ∨
      A.Infinite ∨ B.Infinite := by
  intro hcover
  -- Either A is infinite, or B is infinite, or the negation of both having density 0
  by_cases hA : A.Infinite
  · right; left; exact hA
  · by_cases hB : B.Infinite
    · right; right; exact hB
    · -- Both A and B are finite
      -- The key observation: finite A, finite B → A + B is finite
      -- But finite A + B can't cover cofinitely many integers
      left
      intro ⟨_, _⟩
      have hAfin : A.Finite := Set.not_infinite.mp hA
      have hBfin : B.Finite := Set.not_infinite.mp hB
      -- Sumset of finite sets is finite
      have hAB_finite : (A +ₛ B).Finite := by
        unfold Sumset
        have hprod := (hAfin.prod hBfin).image (fun p : ℕ × ℕ => p.1 + p.2)
        apply Set.Finite.subset hprod
        intro n hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_image, Prod.exists, Set.mem_prod]
        obtain ⟨a, ha, b, hb, hab⟩ := hn
        exact ⟨a, b, ⟨ha, hb⟩, hab.symm⟩
      -- If A + B is finite, then ℕ \ (A + B) is infinite (since ℕ is infinite)
      have huniv_minus : (Set.univ \ (A +ₛ B)).Infinite :=
        Set.Infinite.diff Set.infinite_univ hAB_finite
      -- The intersection with {n > 0} is still infinite (removes at most one element)
      unfold CoversAllButFinitely at hcover
      have hinf : (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}).Infinite := by
        apply Set.Infinite.mono _ (huniv_minus.diff (Set.finite_singleton 0))
        intro n hn
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, true_and, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hn ⊢
        exact ⟨hn.1, Nat.pos_of_ne_zero hn.2⟩
      exact hinf hcover

/- ## Connection to Additive Bases -/

/-- A set A is an asymptotic additive basis of order h if
    hA = {a₁ + ... + aₕ : aᵢ ∈ A} covers all sufficiently large n. -/
def IsAsymptoticBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (as : Fin h → ℕ), (∀ i, as i ∈ A) ∧ n = ∑ i, as i

/-- If A +ₛ B covers cofinitely, then A ∪ B is an asymptotic basis of order 2.

**Proof**: If n ∈ A + B, then n = a + b for some a ∈ A ⊆ A ∪ B and b ∈ B ⊆ A ∪ B.
The set of exceptions is finite, so there exists N₀ above which all n are covered. -/
theorem sumset_covers_implies_basis (A B : Set ℕ) :
    CoversAllButFinitely A B → IsAsymptoticBasis (A ∪ B) 2 := by
  intro hcover
  unfold CoversAllButFinitely at hcover
  unfold IsAsymptoticBasis
  -- The complement of A +ₛ B intersected with positive integers is finite
  -- Therefore, there exists a maximum element N₀ in this finite set
  by_cases h_empty : (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}) = ∅
  · -- If empty, then every positive integer is in A +ₛ B
    use 1
    intro n hn
    have h_in : n ∈ (A +ₛ B) := by
      by_contra h_not
      have : n ∈ Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0} := by
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, Set.mem_setOf_eq, true_and]
        exact ⟨h_not, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
      rw [h_empty] at this
      exact this
    unfold Sumset at h_in
    simp only [Set.mem_setOf_eq] at h_in
    obtain ⟨a, ha, b, hb, hab⟩ := h_in
    -- Construct the function Fin 2 → ℕ that gives a and b
    use ![a, b]
    constructor
    · intro i
      fin_cases i
      · simp only [Set.mem_union]; left; exact ha
      · simp only [Set.mem_union]; right; exact hb
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hab
  · -- The complement is nonempty and finite, so it has a maximum
    push_neg at h_empty
    obtain ⟨m, hm⟩ := h_empty
    have hfin := hcover
    -- Get the maximum element of the finite nonempty set
    have hsup := Set.Finite.bddAbove hfin
    have hne : (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}).Nonempty := ⟨m, hm⟩
    obtain ⟨N₀, hN₀⟩ := hsup
    -- For all n > N₀, n is in A +ₛ B
    use N₀ + 1
    intro n hn
    have h_in : n ∈ (A +ₛ B) := by
      by_contra h_not
      have hn_pos : n > 0 := by omega
      have hmem : n ∈ Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0} := by
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, Set.mem_setOf_eq, true_and]
        exact ⟨h_not, hn_pos⟩
      have hle := hN₀ hmem
      omega
    unfold Sumset at h_in
    simp only [Set.mem_setOf_eq] at h_in
    obtain ⟨a, ha, b, hb, hab⟩ := h_in
    use ![a, b]
    constructor
    · intro i
      fin_cases i
      · simp only [Set.mem_union]; left; exact ha
      · simp only [Set.mem_union]; right; exact hb
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hab

/-- Erdős Problem #31 shows: any infinite A becomes an asymptotic basis of
    order 2 when augmented with a density-0 set. -/
theorem infinite_set_augmentable (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensityZero B ∧ IsAsymptoticBasis (A ∪ B) 2 := by
  obtain ⟨B, hB_dense, hcover⟩ := lorentz_theorem A hA
  refine ⟨B, hB_dense, ?_⟩
  exact sumset_covers_implies_basis A B hcover

/- ## Summary

**Problem Status: SOLVED**

Erdős Problem #31 asked whether any infinite set A can be completed to
cover almost all of ℕ using a density-0 set B.

**Answer: YES** (Lorentz 1954)

**Key Results:**
1. For any infinite A ⊆ ℕ, there exists B with density 0 such that
   A + B ⊇ {n : n ≥ N₀} for some N₀.
2. Moreover, B can be chosen with |B ∩ [1,N]| = O(N/log N).
3. This is essentially optimal in general.

**Formalization Status:**
- 1 axiom: lorentz_theorem (the main theorem, Lorentz 1954 construction)
- 0 sorries
- primes_density_zero: PROVED via Chebyshev theta bound

**Implications:**
- Sparse sets can "complete" each other in a very efficient way
- The additive structure of infinite sets is quite flexible
- Related to questions about additive bases

References:
- Lorentz (1954): Original proof
- Erdős-Straus: Original conjecture
- Related to Erdős Problem #221 (similar questions)
-/

end Erdos31
