/-
  Erdős Problem #1000: Generalized Totients and Diophantine Approximation

  Source: https://erdosproblems.com/1000
  Status: SOLVED (by Haight)

  Statement:
  For an infinite sequence A = {n₁ < n₂ < ⋯} of positive integers, define
  φ_A(k) as the count of 1 ≤ m ≤ n_k such that m/n_k in lowest form has
  denominator different from all previous n_j.

  Question: Does there exist A such that
    lim_{N→∞} (1/N) Σ_{k≤N} φ_A(k)/n_k = 0?

  Answer: YES (Haight), contrary to Erdős' expectation.

  Key Results:
  - Cassels (1950): liminf of Cesàro average can be 0
  - Erdős (1964): φ_A(k)/n_k cannot converge to 0; dichotomy: liminf=0 ⟹ limsup=1
  - Haight: Cesàro average CAN vanish, resolving the problem

  Axiom count: 4 (erdos_no_zero_limit, erdos_dichotomy,
    cassels_liminf_zero, haight_resolution)
  Proved: naturalSeq_phiA_eq_totient (filter condition ↔ coprimality + Icc/range bridge)

  Tags: number-theory, diophantine-approximation, totient-function, cesaro-averages
-/

import Mathlib

namespace Erdos1000

open Finset Filter Topology

/- ## Part I: Core Definitions -/

/-- An increasing sequence of positive integers. -/
structure IncreasingSeq where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  pos : ∀ n, 0 < seq n

/-- The reduced denominator of m/n: when m/n is written in lowest terms,
    the denominator is n / gcd(m, n). -/
def reducedDenom (m n : ℕ) : ℕ := n / Nat.gcd m n

/-- The generalized totient φ_A(k): count of 1 ≤ m ≤ n_k such that the
    reduced denominator of m/n_k differs from all previous terms n_j (j < k). -/
noncomputable def phiA (A : IncreasingSeq) (k : ℕ) : ℕ :=
  ((Icc 1 (A.seq k)).filter (fun m =>
    ∀ j : ℕ, j < k → reducedDenom m (A.seq k) ≠ A.seq j)).card

/- ## Part II: Basic Properties -/

/-- φ_A(k) ≤ n_k: counting a subset of {1, ..., n_k}. -/
theorem phiA_le (A : IncreasingSeq) (k : ℕ) : phiA A k ≤ A.seq k := by
  unfold phiA
  calc ((Icc 1 (A.seq k)).filter _).card
      ≤ (Icc 1 (A.seq k)).card := card_filter_le _ _
    _ = _ := by rw [Nat.card_Icc]; omega

/-- φ_A(0) = n_0: no previous terms means no exclusions. -/
theorem phiA_zero (A : IncreasingSeq) : phiA A 0 = A.seq 0 := by
  unfold phiA
  have h : (Icc 1 (A.seq 0)).filter (fun m =>
      ∀ j : ℕ, j < 0 → reducedDenom m (A.seq 0) ≠ A.seq j) = Icc 1 (A.seq 0) := by
    apply filter_true_of_mem
    intro m _
    intro j hj
    omega
  rw [h, Nat.card_Icc]
  omega

/-- The density ratio ρ_A(k) = φ_A(k) / n_k ∈ ℝ. -/
noncomputable def densityRatio (A : IncreasingSeq) (k : ℕ) : ℝ :=
  (phiA A k : ℝ) / (A.seq k : ℝ)

/-- ρ_A(k) ≥ 0. -/
theorem densityRatio_nonneg (A : IncreasingSeq) (k : ℕ) :
    0 ≤ densityRatio A k :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- ρ_A(k) ≤ 1. -/
theorem densityRatio_le_one (A : IncreasingSeq) (k : ℕ) :
    densityRatio A k ≤ 1 := by
  unfold densityRatio
  rw [div_le_one (by exact_mod_cast A.pos k : (0 : ℝ) < ↑(A.seq k))]
  exact_mod_cast phiA_le A k

/-- ρ_A(0) = 1: the first density ratio is always 1. -/
theorem densityRatio_zero (A : IncreasingSeq) :
    densityRatio A 0 = 1 := by
  unfold densityRatio
  rw [phiA_zero]
  exact div_self (by exact_mod_cast (A.pos 0).ne' : (↑(A.seq 0) : ℝ) ≠ 0)

/- ## Part III: Cesàro Average -/

/-- The Cesàro average C_A(N) = (1/N) Σ_{k<N} ρ_A(k). -/
noncomputable def cesaroAvg (A : IncreasingSeq) (N : ℕ) : ℝ :=
  (∑ k in range N, densityRatio A k) / N

/-- C_A(N) ≥ 0 for all N. -/
theorem cesaroAvg_nonneg (A : IncreasingSeq) (N : ℕ) :
    0 ≤ cesaroAvg A N :=
  div_nonneg (sum_nonneg fun k _ => densityRatio_nonneg A k) (Nat.cast_nonneg _)

/-- C_A(N) ≤ 1 for N > 0. -/
theorem cesaroAvg_le_one (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    cesaroAvg A N ≤ 1 := by
  unfold cesaroAvg
  rw [div_le_one (by exact_mod_cast hN : (0 : ℝ) < ↑N)]
  calc ∑ k in range N, densityRatio A k
      ≤ ∑ _ in range N, (1 : ℝ) := sum_le_sum fun k _ => densityRatio_le_one A k
    _ = N := by simp

/- ## Part IV: The Natural Sequence -/

/-- The natural sequence A = {1, 2, 3, ...} (0-indexed: seq(k) = k+1). -/
def naturalSeq : IncreasingSeq where
  seq := fun n => n + 1
  strictMono := fun _ _ h => by omega
  pos := fun _ => by omega

/-- For A = ℕ, φ_A(k) equals Euler's totient φ(k+1).
    The reduced denominator of m/(k+1) is (k+1)/gcd(m, k+1).
    This is in {1,...,k} iff gcd(m, k+1) > 1 (i.e., m not coprime to k+1).
    So φ_A(k) = #{m ≤ k+1 : gcd(m, k+1) = 1} = φ(k+1).

    Proof: For k=0, phiA = 1 = totient(1) by phiA_zero.
    For k≥1 with n=k+2≥2: the filter condition "n/gcd(m,n) ∉ {1,...,n-1}"
    is equivalent to gcd(m,n)=1 (since n/gcd is a divisor of n in [1,n],
    and it equals n iff gcd=1). Then we bridge (Icc 1 n).filter to
    (range n).filter by showing 0 and n are both non-coprime to n≥2. -/
theorem naturalSeq_phiA_eq_totient (k : ℕ) :
    phiA naturalSeq k = Nat.totient (k + 1) := by
  rcases k with _ | k
  · -- k = 0: phiA naturalSeq 0 = 1 = totient 1
    rw [phiA_zero]; native_decide
  · -- k ≥ 1: n = k + 2 ≥ 2
    unfold phiA reducedDenom
    dsimp [naturalSeq]
    -- Step 1: The filter condition "n/gcd(m,n) ≠ j+1 for all j < k+1"
    -- is equivalent to gcd(m, n) = 1
    have hfilt : ∀ m ∈ Icc 1 (k + 2),
        (∀ j : ℕ, j < k + 1 → (k + 2) / Nat.gcd m (k + 2) ≠ j + 1) ↔
        Nat.gcd m (k + 2) = 1 := by
      intro m _
      constructor
      · -- Forward: if n/gcd avoids {1,...,n-1}, then gcd = 1
        intro h
        by_contra hne
        -- gcd ≠ 0 (since n > 0) and gcd ≠ 1, so gcd ≥ 2
        have hg_ne : Nat.gcd m (k + 2) ≠ 0 := by
          intro heq; exact absurd (Nat.gcd_eq_zero_iff.mp heq).2 (by omega)
        -- n/gcd < n (since gcd > 1) and n/gcd ≥ 1 (since gcd divides n)
        have hdiv_lt : (k + 2) / Nat.gcd m (k + 2) < k + 2 :=
          Nat.div_lt_self (by omega) (by omega)
        have hdiv_pos : 0 < (k + 2) / Nat.gcd m (k + 2) :=
          Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right m (k + 2))) (by omega)
        -- So n/gcd ∈ {1,...,k+1}, contradicting h with j = n/gcd - 1
        exact h ((k + 2) / Nat.gcd m (k + 2) - 1) (by omega) (by omega)
      · -- Backward: if gcd = 1, then n/gcd = n = k+2 > j+1 for all j < k+1
        intro hg j hj
        rw [hg, Nat.div_one]; omega
    rw [filter_congr hfilt]
    -- Step 2: Bridge (Icc 1 n).filter (gcd · n = 1) to (range n).filter (gcd n · = 1)
    -- For n ≥ 2: gcd(n,n) = n ≠ 1 and gcd(n,0) = n ≠ 1, so 0 and n are excluded
    -- from both filters, and the coprime elements in {1,...,n-1} are the same.
    suffices h : (Icc 1 (k + 2)).filter (fun m => Nat.gcd m (k + 2) = 1) =
                 (Finset.range (k + 2)).filter (fun m => Nat.gcd (k + 2) m = 1) by
      rw [h]; rfl
    ext m
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · -- Icc → range: m ≤ n ∧ gcd(m,n)=1 → m < n (since gcd(n,n)=n≠1)
      rintro ⟨⟨hm1, hmn⟩, hg⟩
      exact ⟨by rcases eq_or_lt_of_le hmn with rfl | h
               · rw [Nat.gcd_self] at hg; omega
               · exact h,
             by rwa [Nat.gcd_comm]⟩
    · -- range → Icc: m < n ∧ gcd(n,m)=1 → 1 ≤ m (since gcd(n,0)=n≠1)
      rintro ⟨hmn, hg⟩
      rw [Nat.gcd_comm] at hg
      exact ⟨⟨by rcases Nat.eq_zero_or_pos m with rfl | h
                · simp [Nat.gcd_zero_left] at hg; omega
                · exact h,
              le_of_lt hmn⟩, hg⟩

/- ## Part V: Main Predicates -/

/-- A sequence has vanishing Cesàro average if C_A(N) → 0. -/
def VanishingAverage (A : IncreasingSeq) : Prop :=
  Tendsto (cesaroAvg A) atTop (𝓝 0)

/-- A sequence has density tending to zero if ρ_A(k) → 0. -/
def DensityToZero (A : IncreasingSeq) : Prop :=
  Tendsto (densityRatio A) atTop (𝓝 0)

/- ## Part VI: Erdős' Results (1964) -/

/-- Erdős' No-Zero-Limit Theorem: The density ratio ρ_A(k) = φ_A(k)/n_k
    cannot converge to 0 for any sequence A.
    Proof sketch: φ_A(k) ≥ φ(n_k) ≥ c·n_k/log log n_k → ∞ (Mertens). -/
axiom erdos_no_zero_limit (A : IncreasingSeq) : ¬ DensityToZero A

/-- Erdős' Dichotomy: If the density ratio gets arbitrarily close to 0,
    then it also gets arbitrarily close to 1.
    Proof uses the Euler product formula for φ(n)/n and smooth numbers. -/
axiom erdos_dichotomy (A : IncreasingSeq) :
    (∀ ε > 0, ∃ᶠ k in atTop, densityRatio A k < ε) →
    (∀ ε > 0, ∃ᶠ k in atTop, 1 - ε < densityRatio A k)

/- ## Part VII: Cassels' Result (1950) -/

/-- Cassels' theorem: There exists a sequence A such that
    the liminf of the Cesàro average is 0.
    Constructed via continued fraction convergents. -/
axiom cassels_liminf_zero :
    ∃ A : IncreasingSeq, ∀ ε > 0, ∃ᶠ N in atTop, cesaroAvg A N < ε

/- ## Part VIII: Haight's Resolution -/

/-- Haight's Theorem (resolves Erdős' Problem #1000):
    There exists a sequence A such that the Cesàro average converges to 0.
    Construction uses rapidly growing highly composite numbers to force
    the average to zero while individual terms oscillate.
    This contradicts Erdős' conjecture that no such sequence exists. -/
axiom haight_resolution : ∃ A : IncreasingSeq, VanishingAverage A

/- ## Part IX: Corollaries -/

/-- If the Cesàro average vanishes, the density ratio visits near 0 frequently.
    Contrapositive: if ρ ≥ ε eventually, the Cesàro average converges to
    a value ≥ ε, contradicting convergence to 0.
    The formal argument splits the sum at the threshold index K
    and uses the lower bound ε·(N−K)/N → ε. -/
theorem vanishing_avg_visits_zero (A : IncreasingSeq) (hV : VanishingAverage A)
    (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, densityRatio A k < ε := by
  by_contra h
  rw [Filter.not_frequently] at h
  -- h : ∀ᶠ k in atTop, ¬ (densityRatio A k < ε)
  have hev : ∀ᶠ k in atTop, ε ≤ densityRatio A k := h.mono fun k hk => le_of_not_lt hk
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  -- VanishingAverage: eventually C_A(N) < ε/2
  have hV2 : ∀ᶠ N in atTop, cesaroAvg A N < ε / 2 := by
    have hmem : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (half_pos hε)
    have hpre := hV hmem
    -- hpre : cesaroAvg A ⁻¹' Iio (ε/2) ∈ atTop
    exact hpre
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hV2
  -- Take N large enough
  have hN_bound : 2 * K + 1 ≤ max (2 * K + 1) N₀ := le_max_left _ _
  have hN0_bound : N₀ ≤ max (2 * K + 1) N₀ := le_max_right _ _
  set N := max (2 * K + 1) N₀ with hN_def
  have hNK : K < N := by omega
  have hKleN : K ≤ N := Nat.le_of_lt hNK
  have hNpos : (0 : ℕ) < N := by omega
  -- C_A(N) < ε/2
  have h1 : cesaroAvg A N < ε / 2 := hN₀ N hN0_bound
  -- C_A(N) ≥ ε/2 (from the lower bound on the sum)
  have h2 : ε / 2 ≤ cesaroAvg A N := by
    unfold cesaroAvg
    -- Need: ε/2 ≤ (Σ ρ(k)) / N, i.e., ε/2 * N ≤ Σ ρ(k)
    have hNR : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hNpos
    rw [le_div_iff₀ hNR]
    -- Σ_{k<N} ρ(k) ≥ Σ_{K≤k<N} ε = (N-K)·ε ≥ N/2·ε = ε/2·N
    calc ε / 2 * ↑N ≤ ↑(N - K) * ε := by
            have : (K : ℝ) ≤ (N : ℝ) / 2 := by push_cast; linarith
            rw [Nat.cast_sub hKleN]; nlinarith
      _ = ∑ _i ∈ Ico K N, ε := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Ico K N, densityRatio A i :=
            sum_le_sum fun i hi => hK i (mem_Ico.mp hi).1
      _ ≤ ∑ i ∈ range N, densityRatio A i := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro x hx; exact mem_range.mpr (mem_Ico.mp hx).2
            · intro i _ _; exact densityRatio_nonneg A i
  linarith

/-- Haight oscillation: the sequence achieving vanishing Cesàro average
    must have its density ratio oscillate between near 0 and near 1.
    Combines haight_resolution with erdos_dichotomy. -/
theorem haight_oscillation :
    ∃ A : IncreasingSeq, VanishingAverage A ∧
      ∀ ε > 0, (∃ᶠ k in atTop, densityRatio A k < ε) ∧
               (∃ᶠ k in atTop, 1 - ε < densityRatio A k) := by
  obtain ⟨A, hA⟩ := haight_resolution
  exact ⟨A, hA, fun ε hε =>
    ⟨vanishing_avg_visits_zero A hA ε hε,
     erdos_dichotomy A (fun ε' hε' => vanishing_avg_visits_zero A hA ε' hε') ε hε⟩⟩

/-- No sequence has density → 0: a direct consequence of Erdős' theorem.
    This holds regardless of the Cesàro average's behavior. -/
theorem no_density_zero (A : IncreasingSeq) : ¬ DensityToZero A :=
  erdos_no_zero_limit A

/-- Haight's sequence provides a concrete separation between
    pointwise and Cesàro convergence: ρ_A(k) ↛ 0 yet C_A(N) → 0. -/
theorem pointwise_cesaro_gap :
    ∃ A : IncreasingSeq, VanishingAverage A ∧ ¬ DensityToZero A := by
  obtain ⟨A, hA⟩ := haight_resolution
  exact ⟨A, hA, erdos_no_zero_limit A⟩

end Erdos1000
