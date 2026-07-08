/-
  Lp Riesz (σ-finite): shared infrastructure (helpers, integrationCLM_sf, integral_representation_sf, lp_truncation_tendsto_zero, extByZeroCLM).

  Split out of the monolithic `CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean` (S20, researcher-15).
  Rationale: with the S18 drift fixes applied, the combined 1020-line file
  elaborates past the 32GB/40min Docker build envelope, so its error summary
  never flushes. Splitting each ≥300-line theorem into its own file makes each
  piece elaborate independently and within budget, and makes any residual
  Mathlib-drift errors measurable per-file. Same namespace / same public names,
  so downstream imports are unaffected.
-/
import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

theorem indicator_memLp_sf {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (_ : 1 ≤ p) (_ : p ≠ ⊤) : MemLp (E.indicator (1 : α → ℝ)) p μ :=
  memLp_indicator_const p hE 1 (Or.inr hfin)

/-- If `f` is a.e.-strongly-measurable on the restriction to every spanning set of a
σ-finite measure, then it is a.e.-strongly-measurable for the whole measure. Since the
spanning sets cover the space (`⋃ n, spanningSets μ n = univ`) and are countable,
`aestronglyMeasurable_iUnion_iff` reassembles the global witness from the local ones. -/
theorem aestronglyMeasurable_of_restrict_spanningSets (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (h : ∀ n, AEStronglyMeasurable f (μ.restrict (spanningSets μ n))) :
    AEStronglyMeasurable f μ := by
  have hcov := (aestronglyMeasurable_iUnion_iff (f := f) (μ := μ)
    (s := spanningSets μ)).mpr h
  rwa [iUnion_spanningSets, Measure.restrict_univ] at hcov

/-- `Real.sign` is measurable. Mathlib currently exposes no `Real.measurable_sign`, so we
build it directly from the defining nested `if` over the measurable sets `{r | r < 0}` and
`{r | 0 < r}`. -/
theorem measurable_real_sign : Measurable Real.sign := by
  have hdef : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 :=
    funext fun r => rfl
  rw [hdef]
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

theorem lintegral_mul_le_sf (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∫⁻ a, ‖f a * g a‖₊ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
  have hmul : ∀ a, (‖f a * g a‖₊ : ℝ≥0∞) = ‖f a‖ₑ * ‖g a‖ₑ := fun a => by
    rw [← enorm_eq_nnnorm, enorm_mul]
  simp_rw [hmul]
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop, eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    hf.aestronglyMeasurable.enorm hg.aestronglyMeasurable.enorm

theorem integrable_mul_sf (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun a => f a * g a) μ := by
  rw [← memLp_one_iff_integrable]
  refine ⟨hf.aestronglyMeasurable.mul hg.aestronglyMeasurable, ?_⟩
  calc eLpNorm (fun a => f a * g a) 1 μ
      = ∫⁻ a, ‖f a * g a‖₊ ∂μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]; simp only [enorm_eq_nnnorm]
    _ ≤ eLpNorm f p μ * eLpNorm g q μ := lintegral_mul_le_sf p q hpq hp hptop hf hg
    _ < ⊤ := ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top

-- ============================================================================
-- § 1. Integration CLM
-- ============================================================================

noncomputable def integrationCLM_sf (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    (g : α → ℝ) (hg : MemLp g q μ) :
    Lp ℝ p μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ a, (f : α → ℝ) a * g a ∂μ
      map_add' := fun f₁ f₂ => by
        have h1 := integrable_mul_sf p q hpq hp hptop (Lp.memLp f₁) hg
        have h2 := integrable_mul_sf p q hpq hp hptop (Lp.memLp f₂) hg
        rw [← integral_add h1 h2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with a ha
        rw [ha]; simp [Pi.add_apply, add_mul]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul c fun a => (f : α → ℝ) a * g a]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with a ha
        rw [ha]; simp [Pi.smul_apply, smul_eq_mul, mul_assoc] }
    (eLpNorm g q μ).toReal
    (fun f => by
      have hint := integrable_mul_sf p q hpq hp hptop (Lp.memLp f) hg
      calc ‖∫ a, (f : α → ℝ) a * g a ∂μ‖
          ≤ ∫ a, ‖(f : α → ℝ) a * g a‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ (eLpNorm (f : α → ℝ) p μ * eLpNorm g q μ).toReal := by
            rw [integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
            apply ENNReal.toReal_mono
            · exact ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
            · exact lintegral_mul_le_sf p q hpq hp hptop (Lp.memLp f) hg
        _ = (eLpNorm g q μ).toReal * ‖f‖ := by
            rw [ENNReal.toReal_mul, mul_comm]; rfl)

theorem integrationCLM_sf_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    (g : α → ℝ) (hg : MemLp g q μ) (f : Lp ℝ p μ) :
    integrationCLM_sf p q hp hptop hpq g hg f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  simp [integrationCLM_sf, LinearMap.mkContinuous_apply]

-- ============================================================================
-- § 2. Density extension (Step C — PROVED)
-- ============================================================================

theorem integral_representation_sf (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : MemLp g q μ)
    (hagree : ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
      φ ((indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ) :
    ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  classical
  set Λ := integrationCLM_sf p q (le_of_lt hp1) hptop hpq g hg
  set ψ := φ - Λ
  suffices h : ∀ f : Lp ℝ p μ, ψ f = 0 by
    intro f
    have := h f
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at this
    rw [this, integrationCLM_sf_apply]
  intro f
  apply Lp.induction hptop (motive := fun f => ψ f = 0)
  · intro c s hs hμs
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero]
    rw [Lp.simpleFunc.coe_indicatorConst]
    have heq : indicatorConstLp p hs hμs.ne c =
        c • (indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).toLp _ := by
      rw [Lp.ext_iff]
      filter_upwards [indicatorConstLp_coeFn (c := c),
        Lp.coeFn_smul c ((indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).toLp _),
        (indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hxc hxsmul hx1
      rw [hxc, hxsmul, Pi.smul_apply, hx1, smul_eq_mul,
          Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> simp
    have hlhs : φ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul]; congr 1; exact hagree s hs hμs.ne
    have hrhs : Λ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul, integrationCLM_sf_apply]; congr 1
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [(indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp]
          with x hx
      rw [hx]
      simp only [Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp
    rw [hlhs, hrhs]
  · intro f' g' _hf' _hg' _hdisj hPf hPg
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at *
    rw [map_add, map_add, hPf, hPg]
  · exact isClosed_eq ψ.continuous continuous_const

-- ============================================================================
-- § 3. Spanning-set lemmas
-- ============================================================================

theorem mem_spanningSets_eventually [SigmaFinite μ] (a : α) :
    ∀ᶠ n in atTop, a ∈ spanningSets μ n := by
  have ha : a ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]; exact mem_univ a
  rw [mem_iUnion] at ha
  obtain ⟨N, hN⟩ := ha
  exact (eventually_ge_atTop N).mono fun n hn => monotone_spanningSets μ hn hN

theorem pointwise_mul_indicator_tendsto [SigmaFinite μ] (f : α → ℝ) (a : α) :
    Tendsto (fun n : ℕ => f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds (f a)) := by
  have h1 : Tendsto (fun n : ℕ => (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [mem_spanningSets_eventually (μ := μ) a] with n hn using indicator_of_mem hn _
  simpa using h1.const_mul (f a)

-- ============================================================================
-- § 4. Lp truncation convergence (Step B — PROVED)
-- ============================================================================

theorem lp_truncation_tendsto_zero [SigmaFinite μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} (hf : MemLp f p μ) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm (fun a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a) p μ)
      atTop (nhds 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hinv : 0 < p.toReal⁻¹ := inv_pos.mpr hpr
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop, one_div]
  have key : Tendsto (fun n =>
      ∫⁻ a, (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ)
      atTop (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ∫⁻ a : α, (0 : ℝ≥0∞) ∂μ from by simp]
    apply tendsto_lintegral_of_dominated_convergence' (bound := fun a => (‖f a‖₊ : ℝ≥0∞) ^ p.toReal)
    · intro n
      simp only [← enorm_eq_nnnorm]
      exact ((hf.aestronglyMeasurable.sub
        (hf.aestronglyMeasurable.mul
          (measurable_const.indicator (measurableSet_spanningSets μ n) |>.aestronglyMeasurable))
        ).enorm.pow_const p.toReal)
    · intro n
      filter_upwards [] with a
      apply ENNReal.rpow_le_rpow _ (le_of_lt hpr)
      simp only [ENNReal.coe_le_coe, Set.indicator_apply]
      by_cases h : a ∈ spanningSets μ n <;> simp [h]
    · -- ∫⁻ ↑‖f‖₊ ^ p.toReal ∂μ ≠ ⊤
      have hfin := hf.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop] at hfin
      simp only [← enorm_eq_nnnorm]
      intro hcon
      rw [hcon, ENNReal.top_rpow_of_pos (one_div_pos.mpr hpr)] at hfin
      exact lt_irrefl _ hfin
    · filter_upwards [] with a
      have h1 : Tendsto (fun n => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
          atTop (nhds 0) := by
        have h := (pointwise_mul_indicator_tendsto (μ := μ) f a).const_sub (f a)
        simpa only [sub_self] using h
      have h2 : Tendsto (fun n => (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
          : ℝ≥0∞)) atTop (nhds 0) := by
        have h := h1.nnnorm
        simp only [nnnorm_zero] at h
        simpa using ENNReal.tendsto_coe.mpr h
      have h3 : Tendsto (fun n => (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
          : ℝ≥0∞) ^ p.toReal) atTop (nhds ((0 : ℝ≥0∞) ^ p.toReal)) :=
        h2.ennrpow_const p.toReal
      simpa [ENNReal.zero_rpow_of_pos hpr] using h3
  have h4 : Tendsto (fun n => (∫⁻ a, (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
      : ℝ≥0∞) ^ p.toReal ∂μ) ^ p.toReal⁻¹) atTop (nhds ((0 : ℝ≥0∞) ^ p.toReal⁻¹)) :=
    key.ennrpow_const p.toReal⁻¹
  simpa [ENNReal.zero_rpow_of_pos hinv] using h4

-- ============================================================================
-- § 4.5. Extension-by-zero infrastructure
-- ============================================================================

/-- eLpNorm of S.indicator f under μ equals eLpNorm of f under μ.restrict S. -/
theorem eLpNorm_indicator_eq_restrict_loc {S : Set α} (hS : MeasurableSet S)
    (f : α → ℝ) {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp hptop
  classical
  simp only [eLpNorm_eq_lintegral_rpow_enorm hp hptop]
  congr 1
  rw [show (fun a => ‖S.indicator f a‖ₑ ^ p.toReal) =
      S.indicator (fun a => ‖f a‖ₑ ^ p.toReal) from by
    ext a; simp only [Set.indicator_apply]; split_ifs with ha
    · rfl
    · simp [ENNReal.zero_rpow_of_pos hpr]]
  exact lintegral_indicator hS _

/-- If f ∈ Lp(μ.restrict S), then S.indicator f ∈ Lp(μ). -/
theorem memLp_indicator_of_restrict_loc {S : Set α} (hS : MeasurableSet S)
    {f : α → ℝ} {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤)
    (hf : MemLp f p (μ.restrict S)) : MemLp (S.indicator f) p μ := by
  constructor
  · exact (aestronglyMeasurable_indicator_iff hS).mpr hf.1
  · rw [eLpNorm_indicator_eq_restrict_loc hS _ hp hptop]; exact hf.2

/-- Extension-by-zero: isometric embedding Lp(μ.restrict S) →L[ℝ] Lp(μ).

    Exposed (no longer `private`) so the arbitrary-measure synthesis file
    (`CauchySchwarzIntegralLpDualitySynthesis.lean`) can pull a functional `φ` on
    `Lp ℝ p μ` back to `Lp ℝ p (μ.restrict S)` and invoke the σ-finite Riesz theorem
    on each σ-finite-supporting set `S` (step 1 of the maximality reduction). -/
noncomputable def extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) [Fact (1 ≤ p)] :
    Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)).toLp _
      map_add' := fun f₁ f₂ => by
        rw [Lp.ext_iff]
        filter_upwards [
          (memLp_indicator_of_restrict_loc hS hp hptop
            (Lp.memLp (f₁ + f₂))).coeFn_toLp,
          (memLp_indicator_of_restrict_loc hS hp hptop
            (Lp.memLp f₁)).coeFn_toLp,
          (memLp_indicator_of_restrict_loc hS hp hptop
            (Lp.memLp f₂)).coeFn_toLp,
          Lp.coeFn_add
            ((memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f₁)).toLp _)
            ((memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f₂)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        classical
        rw [h12, hadd]
        simp only [Pi.add_apply]
        rw [h1, h2]
        simp only [Set.indicator_apply]
        split_ifs with ha
        · exact hinner ha
        · ring
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [
          (memLp_indicator_of_restrict_loc hS hp hptop
            (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_indicator_of_restrict_loc hS hp hptop
            (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c
            ((memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        classical
        rw [hcf, RingHom.id_apply, hsmul]
        simp only [Pi.smul_apply]
        rw [hf]
        simp only [Set.indicator_apply, smul_eq_mul]
        split_ifs with ha
        · simp [hinner ha]
        · simp }
    1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have hh := memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)
      have heq : ‖hh.toLp _‖ = ‖f‖ := by
        simp only [Lp.norm_def]
        congr 1
        rw [eLpNorm_congr_ae hh.coeFn_toLp,
            eLpNorm_indicator_eq_restrict_loc hS _ hp hptop]
      exact heq.le)


end RieszSigmaFiniteComplete

end
