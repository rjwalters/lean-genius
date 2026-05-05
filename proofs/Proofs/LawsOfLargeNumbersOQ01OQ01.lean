/-
  SLLN Necessity: Kolmogorov's Converse Direction (laws-of-large-numbers-oq-01-oq-01)

  Theorem: If i.i.d. ℝ-valued random variables satisfy the Strong Law of Large Numbers
  (their Cesàro averages converge a.s.), then they have finite first moment E[|X|] < ∞.

  This proves the `slln_necessity` axiom from LawsOfLargeNumbersOQ01.lean, completing
  Kolmogorov's characterization: SLLN holds ⟺ E[|X₀|] < ∞.

  Proof outline:
  1. Assume ¬Integrable(X₀). Layer cake: Σ_n P(|X₀| > n) = ∞.
  2. By identical distributions: Σ_n P(|Xₙ| > n) = ∞.
  3. Events {|Xₙ| > n} are pairwise independent (from IndepFun, via Kernel API).
  4. Borel-Cantelli 2nd lemma (pairwise independence, variance/Chebyshev argument):
     P(|Xₙ| > n i.o.) = 1.
  5. But SLLN → Xₙ/n → 0 a.s. → P(|Xₙ| > n eventually) = 1 → contradiction.

  Status: Main theorem proved modulo two supporting lemmas:
  - `variance_sum_indicator_le`: variance bound for pairwise-independent indicators
  - `borel_cantelli_pairwise_indep`: BC2 for pairwise-independent events
  Both require the pairwise-independent Borel-Cantelli L² argument.
-/
import Mathlib

namespace LawsOfLargeNumbersOQ01OQ01

open MeasureTheory ProbabilityTheory Filter ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-! ## Layer Cake Formula -/

/-- Integrability implies finite tail sum: E[‖X‖] < ∞ → Σ P(‖X‖ > n) < ∞. -/
theorem tsum_prob_norm_gt_lt_top_of_integrable
    (X : Ω → ℝ) (hmeas : Measurable X) (hint : Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ⊤ := by
  have h_summable : ∑' k : ℕ, μ {ω | ‖X ω‖ > (k : ℝ)} =
      ∫⁻ ω, (∑' k : ℕ, if ‖X ω‖ > (k : ℝ) then 1 else 0) ∂μ := by
    rw [MeasureTheory.lintegral_tsum]
    · congr! 2 with k
      erw [MeasureTheory.lintegral_indicator]
      · aesop
      · exact measurableSet_lt measurable_const hmeas.norm
    · exact fun n => Measurable.aemeasurable
        (Measurable.ite (measurableSet_lt measurable_const hmeas.norm)
          measurable_const measurable_const)
  have h_inner_bound : ∀ ω : Ω,
      ∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0) ≤ ‖X ω‖ + 1 := by
    intro ω
    have hle : ∑' k : ℕ, (if ‖X ω‖ > (k : ℝ) then 1 else 0) ≤
        ∑ k ∈ Finset.range (Nat.floor (‖X ω‖) + 1), (1 : ℝ) := by
      rw [tsum_eq_sum]
      · exact Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      · exact fun n hn => if_neg (by exact fun h => hn (Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.le_floor (mod_cast h.le)))))
    exact hle.trans (by simpa using Nat.floor_le (norm_nonneg (X ω)))
  have h_integral_finite : ∫⁻ ω, (∑' k : ℕ, if ‖X ω‖ > (k : ℝ) then 1 else 0) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (‖X ω‖ + 1) ∂μ := by
    apply MeasureTheory.lintegral_mono fun ω => ?_
    convert ENNReal.ofReal_le_ofReal (h_inner_bound ω) using 1
    · norm_num [ENNReal.ofReal]
      rw [tsum_eq_sum]
      any_goals exact Finset.range (⌊|X ω|⌋₊ + 1)
      · rw [tsum_eq_sum]; aesop
        exact fun n hn => if_neg fun h => hn (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.le_floor (mod_cast h.le))))
      · exact fun n hn => if_neg fun h => hn (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.le_floor (mod_cast h.le))))
  simp only [Set.mem_Ioi] at *
  exact h_summable ▸ lt_of_le_of_lt h_integral_finite
    (by convert MeasureTheory.Integrable.lintegral_lt_top
          (MeasureTheory.Integrable.add hint.norm (MeasureTheory.integrable_const _)))

/-- Finite tail sum implies integrability: Σ P(‖X‖ > n) < ∞ → Integrable X. -/
theorem integrable_of_tsum_prob_norm_gt_lt_top
    (X : Ω → ℝ) (hmeas : Measurable X)
    (htsum : (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ∞) :
    Integrable X μ := by
  contrapose htsum
  have h_fubini : ∫⁻ (ω : Ω), ⌈‖X ω‖⌉₊ ∂μ = ∑' (n : ℕ), μ {ω | ‖X ω‖ > n} := by
    have heq : ∫⁻ (ω : Ω), ⌈‖X ω‖⌉₊ ∂μ =
        ∫⁻ (ω : Ω), ∑' (n : ℕ), (if n < ‖X ω‖ then 1 else 0) ∂μ := by
      congr with ω
      rw [tsum_eq_sum]
      any_goals exact Finset.range ⌈‖X ω‖⌉₊
      · rw [Finset.sum_congr rfl fun i hi => if_pos (Nat.lt_ceil.mp (Finset.mem_range.mp hi))]
        aesop
      · aesop
    rw [heq, MeasureTheory.lintegral_tsum]
    · congr with n
      erw [MeasureTheory.lintegral_indicator]
      · aesop
      · exact measurableSet_lt measurable_const hmeas.norm
    · exact fun n => Measurable.aemeasurable
        (Measurable.ite (measurableSet_lt measurable_const hmeas.norm)
          measurable_const measurable_const)
  contrapose! htsum
  simp only [MeasureTheory.Integrable, not_and, Set.mem_Ioi] at *
  intro _
  simp only [MeasureTheory.hasFiniteIntegral_iff_norm] at *
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ω => ?_) (h_fubini ▸ htsum)
  rw [ENNReal.ofReal_le_iff_le_toReal] <;> norm_num [Nat.le_ceil]

/-- Non-integrability implies infinite tail sum: ¬Integrable X → Σ P(‖X‖ > n) = ∞. -/
theorem tsum_prob_norm_gt_eq_top_of_not_integrable
    (X : Ω → ℝ) (hmeas : Measurable X) (hint : ¬Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤ := by
  by_contra h_contra
  exact hint (integrable_of_tsum_prob_norm_gt_lt_top X hmeas (lt_top_iff_ne_top.mpr h_contra))

/-! ## Cesàro Argument -/

/-- If Cesàro averages (1/n) Σ_{i<n} u_i → c, then u_n/n → 0. -/
theorem tendsto_zero_div_of_cesaro
    {u : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, u i) atTop (nhds c)) :
    Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • u n) atTop (nhds 0) := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, u i
  have hS : Tendsto (fun n => S n / (n : ℝ)) atTop (nhds c) := by
    simpa [div_eq_inv_mul] using h
  have h_diff : Tendsto (fun n => (S (n + 1) - S n) / (n : ℝ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n =>
        (S (n + 1) / (n + 1 : ℝ)) * ((n + 1 : ℝ) / (n : ℝ)) - S n / (n : ℝ))
        atTop (nhds 0) := by
      simpa using Tendsto.sub
        (Tendsto.mul (hS.comp (tendsto_add_atTop_nat 1))
          (show Tendsto (fun n : ℕ => (n + 1 : ℝ) / n) atTop (nhds 1) by
            simpa [add_div] using
              tendsto_const_nhds.add tendsto_inverse_atTop_nhds_zero_nat
              |>.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with n hn; aesop)))
        hS
    refine h1.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with n hn;
      rw [div_mul_div_cancel₀ (by positivity)]; ring)
  simp only [smul_eq_mul] at *
  simpa [div_eq_inv_mul, Finset.sum_range_succ] using h_diff

/-! ## Borel-Cantelli for Pairwise Independent Events -/

/-- Variance of sum of pairwise-independent indicators is bounded by sum of probabilities.

    For pairwise-independent events A₁, ..., Aₙ with t a finite index set:
      Var[Σᵢ∈t 1_{Aᵢ}] = Σᵢ∈t Var[1_{Aᵢ}] ≤ Σᵢ∈t P(Aᵢ).

    Proof: Off-diagonal covariances vanish by pairwise independence;
    diagonal variances satisfy Var[1_A] = P(A)(1-P(A)) ≤ P(A). -/
theorem variance_sum_indicator_le
    {ι : Type*} {t : Finset ι} {s : ι → Set Ω}
    (hmeas : ∀ i ∈ t, MeasurableSet (s i))
    (hindep : Set.Pairwise t (fun i j => IndepSet (s i) (s j) μ)) :
    variance (∑ i ∈ t, (s i).indicator (fun _ => 1)) μ ≤ ∑ i ∈ t, (μ (s i)).toReal := by
  sorry

/-- Borel-Cantelli 2nd lemma for pairwise-independent events.

    If events {Aₙ} are pairwise independent with Σ P(Aₙ) = ∞, then P(Aₙ i.o.) = 1.

    Proof: Let Sₙ = Σᵢ<ₙ 1_{Aᵢ}. Then E[Sₙ] = Σᵢ<ₙ P(Aᵢ) → ∞.
    By `variance_sum_indicator_le`: Var[Sₙ] ≤ E[Sₙ].
    By Chebyshev: P(Sₙ ≤ M) ≤ 4/E[Sₙ] → 0 for all M.
    Monotone Sₙ with P(Sₙ ≤ M) → 0 implies Sₙ → ∞ a.s., i.e., Aₙ i.o. a.s. -/
theorem borel_cantelli_pairwise_indep
    {s : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (s n))
    (hindep : Pairwise (fun i j => IndepSet (s i) (s j) μ))
    (hsum : ∑' n, μ (s n) = ⊤) :
    μ (Filter.limsup s atTop) = 1 := by
  sorry

/-! ## Main Theorem -/

/-- **Kolmogorov SLLN Necessity**: If i.i.d. measurable random variables satisfy the SLLN,
    then they have finite first moment.

    Statement: (∃ c, ∀ᵐ ω, (1/n) Σ_{i<n} X_i(ω) → c) implies Integrable (X 0) μ.

    This converts the `slln_necessity` axiom in LawsOfLargeNumbersOQ01.lean into a theorem,
    completing Kolmogorov's characterization: SLLN ⟺ E[|X₀|] < ∞.

    Note: The measurability hypothesis follows from `IdentDistrib` (which provides
    AEMeasurability), lifted to Measurability for Borel-standard probability spaces. -/
theorem slln_necessity
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
        atTop (nhds c)) :
    Integrable (X 0) μ := by
  by_contra h_not_int
  -- Step 1: Layer cake: ¬Integrable(X₀) → Σ P(‖X₀‖ > n) = ∞
  have h_sum_inf : (∑' n : ℕ, μ {ω : Ω | ‖X 0 ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤ :=
    tsum_prob_norm_gt_eq_top_of_not_integrable (X 0) (hmeas 0) h_not_int
  -- Step 2: Σ P(‖Xₙ‖ > n) = ∞ by identical distributions
  have h_sum_iid : (∑' n : ℕ, μ {ω | (↑n : ℝ) < ‖X n ω‖}) = ⊤ := by
    have h : (∑' n : ℕ, μ {ω : Ω | ‖X n ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤ := by
      convert h_sum_inf using 2 with n
      exact (hident n).measure_mem_eq (measurableSet_lt measurable_const measurable_norm)
    simpa [Set.mem_Ioi] using h
  -- Step 3: Pairwise independence of events {‖Xₙ‖ > n}
  have h_indep_events : Pairwise (fun i j =>
      IndepSet {ω | (↑i : ℝ) < ‖X i ω‖} {ω | (↑j : ℝ) < ‖X j ω‖} μ) := by
    intro i j hij
    have h := hindep hij
    simp_all only [ProbabilityTheory.IndepFun, ProbabilityTheory.IndepSet]
    rw [ProbabilityTheory.Kernel.indepSet_iff_measure_inter_eq_mul] at *
    · rw [ProbabilityTheory.Kernel.indepFun_iff_measure_inter_preimage_eq_mul] at h
      convert h {x : ℝ | (↑i : ℝ) < ‖x‖} {x : ℝ | (↑j : ℝ) < ‖x‖}
        (measurableSet_lt measurable_const measurable_norm)
        (measurableSet_lt measurable_const measurable_norm) using 1
    · exact measurableSet_lt measurable_const (hmeas i).norm
    · exact measurableSet_lt measurable_const (hmeas j).norm
  -- Step 4: BC2 → P(‖Xₙ‖ > n i.o.) = 1
  have h_bc : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∃ n ≥ N, ‖X n ω‖ > n := by
    have h_bc_meas : μ (Filter.limsup (fun n => {ω | (↑n : ℝ) < ‖X n ω‖}) atTop) = 1 :=
      borel_cantelli_pairwise_indep
        (fun n => measurableSet_lt measurable_const (hmeas n).norm)
        h_indep_events
        (by exact h_sum_iid)
    simp_all only [Filter.limsup_eq_iInf_iSup_of_nat]
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (show μ (⋂ n : ℕ, ⋃ i : ℕ, ⋃ (_ : n ≤ i), {ω : Ω | (↑i : ℝ) < ‖X i ω‖})ᶜ = 0 by
        rw [MeasureTheory.measure_compl
          (MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ =>
            MeasurableSet.iUnion fun _ =>
              measurableSet_lt measurable_const (hmeas _ |>.norm))
          (MeasureTheory.measure_ne_top _ _)]
        aesop)] with ω hω N
    aesop
  -- Step 5: SLLN → Xₙ/n → 0 a.s.
  obtain ⟨c, hc⟩ := hslln
  have h_cesaro : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω / (n : ℝ)) atTop (nhds 0) := by
    filter_upwards [hc] with ω hω
    have := tendsto_zero_div_of_cesaro hω
    simpa [div_eq_inv_mul] using this
  have h_zero : ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, ‖X n ω‖ ≤ n := by
    filter_upwards [h_cesaro] with ω hω
    rcases Metric.tendsto_atTop.mp hω 1 zero_lt_one with ⟨N, hN⟩
    exact ⟨N + 1, fun n hn => by
      have h1 := hN n (by linarith)
      rw [dist_zero_right] at h1
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] at h1
      rw [div_lt_one (by norm_cast; linarith)] at h1
      linarith⟩
  -- Step 6: Contradiction
  exact absurd (h_bc.and h_zero)
    (by intro H
        obtain ⟨ω, hω₁, hω₂⟩ := H.exists
        obtain ⟨N, hN⟩ := hω₂
        obtain ⟨n, hn₁, hn₂⟩ := hω₁ N
        exact hn₂.not_le (hN n hn₁))

end LawsOfLargeNumbersOQ01OQ01
