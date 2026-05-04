/-
# Lp Riesz Representation for Sigma-Finite Measures (Complete)
(cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01-incomplete-01)

## What This Proves

This file advances the sigma-finite generalization of the Riesz Lp representation theorem.
Steps B (Lp truncation convergence) and C (density extension) are proved.
Step A (localization_existence) has one remaining sorry for the MCT/consistency step.

### Results Proved (no sorry)

1. `integrationCLM_sf`: Integration CLM on Lp(μ), IsFiniteMeasure dropped.
2. `integral_representation_sf`: Step C via Lp.induction (sigma-finite μ).
3. `lp_truncation_tendsto_zero`: Step B via dominated convergence.
4. `eLpNorm_indicator_eq_restrict_loc`: eLpNorm(S.indicator f, μ) = eLpNorm(f, μ.restrict S).
5. `memLp_indicator_of_restrict_loc`: MemLp for indicator from restriction.
6. `extByZeroCLM`: Extension-by-zero CLM, Lp(μ.restrict S) →L[ℝ] Lp(μ).
7. `riesz_lp_surjective_sigma_finite`: Main theorem (assuming Step A).

### Sorries Remaining (1)

- `localization_existence` (Step A): MCT/consistency for global g ∈ Lq(μ).
  The extByZeroCLM + finite-measure Riesz structure is in place.

## References

- Folland, Real Analysis (2nd ed.), Theorem 6.15
- Mathlib: `MeasureTheory.Lp.induction`, `MeasureTheory.SigmaFinite.spanningSets`
-/

import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

-- ============================================================================
-- § 0. Helper lemmas
-- ============================================================================

/-- 1_E ∈ Lp(μ) for μ(E) < ∞. -/
theorem indicator_memLp_sf {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (_ : 1 ≤ p) (_ : p ≠ ⊤) : MemLp (E.indicator (1 : α → ℝ)) p μ :=
  memLp_indicator_const p hE 1 (Or.inr hfin)

theorem lintegral_mul_le_sf (p q : ℝ≥0∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} {g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ∫⁻ a, ‖f a * g a‖₊ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
  have hqtop : q ≠ ⊤ := by
    intro hq; rw [hq, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
  have hmul : ∀ a, (‖f a * g a‖₊ : ℝ≥0∞) = (‖f a‖₊ : ℝ≥0∞) * ‖g a‖₊ := fun a => by
    simp only [← ENNReal.coe_mul, nnnorm_mul]
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
      = ∫⁻ a, ‖f a * g a‖₊ ∂μ := by simp [eLpNorm, eLpNorm']
    _ ≤ eLpNorm f p μ * eLpNorm g q μ := lintegral_mul_le_sf p q hpq hp hptop hf hg
    _ < ⊤ := ENNReal.mul_lt_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne

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
        simp only [Lp.coeFn_add, Pi.add_apply, add_mul]
        exact integral_add h1 h2
      map_smul' := fun c f => by
        simp only [Lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show (fun a => c * (f : α → ℝ) a * g a) = (fun a => c * ((f : α → ℝ) a * g a))
            from by ext a; ring]
        exact integral_const_mul c _ }
    (eLpNorm g q μ).toReal
    (fun f => by
      have hint := integrable_mul_sf p q hpq hp hptop (Lp.memLp f) hg
      calc ‖∫ a, (f : α → ℝ) a * g a ∂μ‖
          ≤ ∫ a, ‖(f : α → ℝ) a * g a‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ (eLpNorm (f : α → ℝ) p μ * eLpNorm g q μ).toReal := by
            rw [← integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
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
      filter_upwards [indicatorConstLp_coeFn,
        Lp.coeFn_smul c ((indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).toLp _),
        (indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hxc hxsmul hx1
      rw [hxc, hxsmul, Pi.smul_apply, hx1, smul_eq_mul,
          Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring
    have hlhs : φ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul]; congr 1; exact hagree s hs hμs.ne
    have hrhs : Λ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul, integrationCLM_sf_apply]; congr 1
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [(indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp]
          with x hx
      rw [hx, Set.indicator_apply, Set.indicator_apply]; split_ifs <;> ring
    rw [hlhs, hrhs]
  · intro f' g' _hf' _hg' _hdisj hPf hPg
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at *
    rw [map_add, map_add, hPf, hPg]
  · exact isClosed_eq ψ.continuous continuous_const
  exact f

-- ============================================================================
-- § 3. Spanning-set lemmas
-- ============================================================================

theorem mem_spanningSets_eventually [SigmaFinite μ] (a : α) :
    ∀ᶠ n in atTop, a ∈ spanningSets μ n := by
  have ha : a ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]; exact mem_univ a
  rw [mem_iUnion] at ha
  obtain ⟨N, hN⟩ := ha
  exact (eventually_ge_atTop N).mono fun n hn => spanningSets_mono μ hn hN

theorem pointwise_mul_indicator_tendsto [SigmaFinite μ] (f : α → ℝ) (a : α) :
    Tendsto (fun n : ℕ => f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds (f a)) := by
  have h1 : Tendsto (fun n : ℕ => (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [mem_spanningSets_eventually a] with n hn using indicator_of_mem hn _
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
  simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm hp0 hptop, one_div]
  have key : Tendsto (fun n =>
      ∫⁻ a, (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ)
      atTop (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ∫⁻ a : α, (0 : ℝ≥0∞) ∂μ from by simp]
    apply tendsto_lintegral_of_dominated_convergence (bound := fun a => (‖f a‖₊ : ℝ≥0∞) ^ p.toReal)
    · intro n
      exact ((hf.aestronglyMeasurable.sub
        (hf.aestronglyMeasurable.mul
          (measurable_const.indicator (measurableSet_spanningSets μ n) |>.aestronglyMeasurable))
        ).enorm.pow_const p.toReal)
    · intro n
      filter_upwards [] with a
      apply ENNReal.rpow_le_rpow _ (le_of_lt hpr)
      simp only [ENNReal.coe_le_coe, Set.indicator_apply]
      by_cases h : a ∈ spanningSets μ n <;> simp [h]
    · rw [← eLpNorm_eq_lintegral_rpow_nnnorm hp0 hptop]
      exact hf.eLpNorm_lt_top.ne
    · filter_upwards [] with a
      have h1 : Tendsto (fun n => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
          atTop (nhds 0) := by
        have h := (pointwise_mul_indicator_tendsto f a).const_sub (f a)
        simpa only [sub_self] using h
      have h2 : Tendsto (fun n => (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
          : ℝ≥0∞)) atTop (nhds 0) := by
        have := h1.nnnorm; simp only [nnnorm_zero] at this; exact_mod_cast this
      have h3 : Tendsto (fun n => (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
          : ℝ≥0∞) ^ p.toReal) atTop (nhds ((0 : ℝ≥0∞) ^ p.toReal)) :=
        (ENNReal.continuousAt_rpow_const (Or.inl (le_of_lt hpr))).tendsto.comp h2
      simpa [ENNReal.zero_rpow_of_pos hpr] using h3
  have h4 : Tendsto (fun n => (∫⁻ a, (‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖₊
      : ℝ≥0∞) ^ p.toReal ∂μ) ^ p.toReal⁻¹) atTop (nhds ((0 : ℝ≥0∞) ^ p.toReal⁻¹)) :=
    (ENNReal.continuousAt_rpow_const (Or.inl hinv.le)).tendsto.comp key
  simpa [ENNReal.zero_rpow_of_pos hinv] using h4

-- ============================================================================
-- § 4.5. Extension-by-zero infrastructure
-- ============================================================================

/-- eLpNorm of S.indicator f under μ equals eLpNorm of f under μ.restrict S. -/
private theorem eLpNorm_indicator_eq_restrict_loc {S : Set α} (hS : MeasurableSet S)
    (f : α → ℝ) {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp hptop
  simp only [eLpNorm_eq_lintegral_rpow_nnnorm hp hptop]
  congr 1
  rw [show (fun a => (‖S.indicator f a‖₊ : ℝ≥0∞) ^ p.toReal) =
      S.indicator (fun a => (‖f a‖₊ : ℝ≥0∞) ^ p.toReal) from by
    ext a; simp only [Set.indicator_apply]; split_ifs with ha
    · rfl
    · simp [ENNReal.zero_rpow_of_pos hpr]]
  exact lintegral_indicator hS _

/-- If f ∈ Lp(μ.restrict S), then S.indicator f ∈ Lp(μ). -/
private theorem memLp_indicator_of_restrict_loc {S : Set α} (hS : MeasurableSet S)
    {f : α → ℝ} {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤)
    (hf : MemLp f p (μ.restrict S)) : MemLp (S.indicator f) p μ := by
  constructor
  · exact (aestronglyMeasurable_indicator_iff hS).mpr hf.1
  · rw [eLpNorm_indicator_eq_restrict_loc hS _ hp hptop]; exact hf.2

/-- Extension-by-zero: isometric embedding Lp(μ.restrict S) →L[ℝ] Lp(μ). -/
private noncomputable def extByZeroCLM {S : Set α} (hS : MeasurableSet S)
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
            (memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f₁)).toLp _
            (memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f₂)).toLp _,
          (Measure.ae_restrict_iff' hS).mp (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        rw [h12, hadd, h1, h2]
        simp only [Set.indicator_apply, Pi.add_apply]
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
            (memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)).toLp _,
          (Measure.ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        rw [hcf, hsmul, hf, RingHom.id_apply]
        simp only [Set.indicator_apply, Pi.smul_apply]
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

-- ============================================================================
-- § 5. Localization step (Step A — 1 sorry)
-- ============================================================================

/-- **Step A**: constructs g ∈ Lq(μ) with indicator agreement on finite-measure sets.

    Proof outline (Folland §6.2):
    1. For each n, μ.restrict(Sₙ) is finite. Build φₙ = φ ∘ extByZeroCLM.
    2. Apply `RieszLpSurjectivity.riesz_lp_surjective_from_rn` to get gₙ ∈ Lq(μₙ).
    3. Consistency: gₙ₊₁ = gₙ a.e. on Sₙ (Lq uniqueness).
    4. MCT + uniform bound ‖gₙ‖_{Lq(μₙ)} ≤ ‖φₙ‖ ≤ ‖φ‖ gives g ∈ Lq(μ).
    5. Indicator agreement via continuity of φ and DCT.
    Infrastructure (extByZeroCLM, finite-measure application) is proved above.
    Remaining sorry: MCT/consistency for global g. -/
theorem localization_existence
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
        φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
        ∫ a in E, g a ∂μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_of_lt hp1))
  -- For each n, finite-measure Riesz on μ.restrict(Sₙ) via φₙ = φ ∘ extByZeroCLM
  have hriesz_n : ∀ n, ∃ gₙ : α → ℝ,
      MemLp gₙ q (μ.restrict (spanningSets μ n)) ∧
      ∀ f : Lp ℝ p (μ.restrict (spanningSets μ n)),
        φ (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop f) =
        ∫ a, (f : α → ℝ) a * gₙ a ∂(μ.restrict (spanningSets μ n)) := by
    intro n
    haveI hfin_n : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      { measure_univ_lt_top := by
          have : (μ.restrict (spanningSets μ n)) Set.univ =
              μ (spanningSets μ n) := by
            rw [Measure.restrict_apply MeasurableSet.univ, Set.inter_univ]
          rw [this]; exact measure_spanningSets_lt_top μ n }
    haveI : SigmaFinite (μ.restrict (spanningSets μ n)) := inferInstance
    let φₙ : Lp ℝ p (μ.restrict (spanningSets μ n)) →L[ℝ] ℝ :=
      φ.comp (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop)
    obtain ⟨gₙ, hgₙ, hgₙ_rep⟩ :=
      RieszLpSurjectivity.riesz_lp_surjective_from_rn p q hp1 hptop hpq φₙ
    exact ⟨gₙ, hgₙ, hgₙ_rep⟩
  -- Extract the gₙ family
  choose g_seq hg_seq_mem hg_seq_rep using hriesz_n
  -- Key: extByZeroCLM(Sₙ)(1_E^Lp(μₙ)) = 1_E^Lp(μ), for E ⊆ Sₙ
  -- (Both have representative E.indicator 1 a.e. w.r.t. μ)
  have hext_ind : ∀ n (E : Set α) (hE : MeasurableSet E) (hEn : E ⊆ spanningSets μ n)
      (hfin : μ E ≠ ⊤),
      extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop
        ((memLp_indicator_const p hE 1 (Or.inr (show (μ.restrict (spanningSets μ n)) E ≠ ⊤ from by
            rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin))).toLp _) =
      (memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ := by
    intro n E hE hEn hfin
    have hfin_n : (μ.restrict (spanningSets μ n)) E ≠ ⊤ := by
      rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin
    rw [Lp.ext_iff]
    -- Show both cofunctions are a.e. E.indicator 1 under μ
    have hlhs : (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop
        ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _) : α → ℝ) =ᵐ[μ]
        (spanningSets μ n).indicator
          ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) :=
      (memLp_indicator_of_restrict_loc (measurableSet_spanningSets μ n) hp0 hptop
        (Lp.memLp _)).coeFn_toLp
    have hrhs : ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ : α → ℝ) =ᵐ[μ]
        E.indicator 1 :=
      (memLp_indicator_const p hE 1 (Or.inr hfin)).coeFn_toLp
    -- Sₙ.indicator (coeFn of 1_E^Lp(μₙ)) =ᵐ[μ] E.indicator 1
    -- coeFn_toLp gives =ᵐ[μ.restrict Sₙ]; convert to =ᵐ[μ] via ae_restrict_iff'
    have hkey : (spanningSets μ n).indicator
        ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) =ᵐ[μ]
        E.indicator 1 := by
      have hcoe_restrict : ∀ᵐ a ∂μ, a ∈ spanningSets μ n →
          (memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ a = E.indicator 1 a :=
        (ae_restrict_iff' (measurableSet_spanningSets μ n)).mp
          (memLp_indicator_const p hE 1 (Or.inr hfin_n)).coeFn_toLp
      filter_upwards [hcoe_restrict] with a ha
      simp only [Set.indicator_apply]
      by_cases hn : a ∈ spanningSets μ n
      · simp only [hn, ite_true]; exact ha hn
      · simp only [hn, ite_false, Set.indicator_apply, if_neg (fun he => hn (hEn he))]
    exact hlhs.trans hkey |>.trans hrhs.symm
  -- For E ⊆ Sₙ with μ(E) < ∞: φ(1_E^Lp(μ)) = ∫_E g_seq n dμ
  have hagree_n : ∀ n (E : Set α) (hE : MeasurableSet E) (hEn : E ⊆ spanningSets μ n)
      (hfin : μ E ≠ ⊤),
      φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
      ∫ a in E, g_seq n a ∂μ := by
    intro n E hE hEn hfin
    have hfin_n : (μ.restrict (spanningSets μ n)) E ≠ ⊤ := by
      rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin
    -- φ(1_E) = φ(extByZeroCLM(1_E^Lp(μₙ))) = ∫ 1_E * g_seq n ∂μₙ = ∫_E g_seq n ∂μ
    rw [← hext_ind n E hE hEn hfin]
    rw [hg_seq_rep n]
    -- ∫ (coeFn of 1_E^Lp(μₙ)) * g_seq n ∂(μ.restrict Sₙ) = ∫_E g_seq n ∂μ
    have hcoe : ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) =ᵐ[μ.restrict (spanningSets μ n)]
        E.indicator 1 :=
      (memLp_indicator_const p hE 1 (Or.inr hfin_n)).coeFn_toLp
    rw [integral_congr_ae (EventuallyEq.mul_right hcoe _)]
    simp_rw [Set.indicator_apply, Pi.one_apply, ite_mul, one_mul, zero_mul]
    rw [integral_indicator hE, Measure.restrict_restrict hE,
      Set.inter_comm, Set.inter_eq_left.mpr hEn]
  -- ── Step A1: Norm bound ─────────────────────────────────────────────────────
  -- HARD sorry: ‖g_seq n‖_{Lq(μ.restrict Sₙ)} ≤ ‖φ‖
  -- Proof sketch: let φₙ := φ ∘ extByZeroCLM(Sₙ); then ‖φₙ‖ ≤ ‖φ‖.
  -- riesz_lp_surjective_from_rn gives g_seq n with ‖g_seq n‖_Lq = ‖φₙ‖ ≤ ‖φ‖.
  -- The equality uses the Hölder extremizer (cf. holder_extremizer_lq_bound in parent).
  have hgnorm : ∀ n, eLpNorm (g_seq n) q (μ.restrict (spanningSets μ n)) ≤
      ENNReal.ofReal ‖φ‖ := by
    intro n
    set μₙ := μ.restrict (spanningSets μ n)
    set hS := measurableSet_spanningSets μ n
    set extZ := extByZeroCLM hS hp0 hptop
    have hg := hg_seq_mem n
    set g := g_seq n
    -- Derived constants
    have hqtop' : q ≠ ⊤ := by
      intro h; rw [h, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
    have hq0' : q ≠ 0 := by
      intro h; rw [h, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
    have hq_pos' : 0 < q.toReal := ENNReal.toReal_pos hq0' hqtop'
    have hp_pos' : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    -- μₙ is finite
    haveI hfin' : IsFiniteMeasure μₙ :=
      { measure_univ_lt_top := by
          simp only [μₙ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_spanningSets_lt_top μ n }
    -- ‖extZ f‖ = ‖f‖ (isometry), hence ‖extZ‖ ≤ 1
    have hextZ_le : ∀ f : Lp ℝ p μₙ, ‖extZ f‖ ≤ ‖f‖ := fun f => by
      simp only [extZ, extByZeroCLM, LinearMap.mkContinuous_apply, Lp.norm_def]
      have hh := memLp_indicator_of_restrict_loc hS hp0 hptop (Lp.memLp f)
      conv_lhs => rw [eLpNorm_congr_ae hh.coeFn_toLp]
      rw [eLpNorm_indicator_eq_restrict_loc hS _ hp0 hptop]
    have hextZ_norm : ‖extZ‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
        rw [one_mul]; exact hextZ_le f)
    have hphin_le : ‖φ.comp extZ‖ ≤ ‖φ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hextZ_norm)
    -- hrep: (φ ∘ extZ) f = ∫ f * g ∂μₙ for all f ∈ Lp(μₙ)
    have hrep : ∀ f : Lp ℝ p μₙ, (φ.comp extZ) f = ∫ a, (f : α → ℝ) a * g a ∂μₙ := by
      intro f; simp only [ContinuousLinearMap.comp_apply]; exact hg_seq_rep n f
    -- For each truncation g_k := clamp(g, -k, k), prove ‖g_k‖_q ≤ ‖φ ∘ extZ‖
    have htrunc : ∀ k : ℕ,
        eLpNorm (fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) q μₙ ≤
        ENNReal.ofReal ‖φ.comp extZ‖ := by
      intro k
      set g_k := fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))
      set h_k := fun a => Real.sign (g_k a) * |g_k a| ^ (q.toReal - 1)
      -- |g_k a| ≤ k
      have hgk_bound : ∀ a, |g_k a| ≤ (k : ℝ) := fun a => by
        simp only [g_k, abs_le]
        constructor
        · linarith [le_max_right (min (g a) (k : ℝ)) (-(k : ℝ))]
        · exact max_le_iff.mpr ⟨min_le_right _ _, neg_le_self (Nat.cast_nonneg k)⟩
      -- g_k is AEStronglyMeasurable and integrable on μₙ
      have hgk_asm : AEStronglyMeasurable g_k μₙ :=
        (hg.1.min measurable_const.aestronglyMeasurable).max
          measurable_const.aestronglyMeasurable
      have hgk_int : Integrable g_k μₙ := by
        rw [← memLp_one_iff_integrable]
        exact MemLp.of_bound (k : ℝ) hgk_asm
          (ae_of_all μₙ fun a => by
            simp only [Real.norm_eq_abs]; exact hgk_bound a)
      -- h_k is bounded and in Lp
      have hhk_bound : ∀ᵐ a ∂μₙ, ‖h_k a‖ ≤ (k : ℝ) ^ (q.toReal - 1) :=
        ae_of_all μₙ fun a => by
          simp only [h_k, Real.norm_eq_abs, abs_mul]
          calc |Real.sign (g_k a)| * |g_k a| ^ (q.toReal - 1)
              ≤ 1 * |g_k a| ^ (q.toReal - 1) :=
                  mul_le_mul_of_nonneg_right (Real.abs_sign_le_one _) (by positivity)
            _ = |g_k a| ^ (q.toReal - 1) := one_mul _
            _ ≤ (k : ℝ) ^ (q.toReal - 1) :=
                  Real.rpow_le_rpow (abs_nonneg _) (hgk_bound a)
                    (by linarith [hpq.symm.one_lt_of_lt hp1])
      have hhk_meas : AEStronglyMeasurable h_k μₙ := by
        apply AEStronglyMeasurable.mul
        · exact (Real.measurable_sign.comp_aemeasurable
              hgk_asm.aemeasurable).aestronglyMeasurable
        · exact hgk_asm.norm.rpow_const _
      have hhk_memLp : MemLp h_k p μₙ :=
        MemLp.of_bound ((k : ℝ) ^ (q.toReal - 1)) hhk_meas hhk_bound
      -- φₙ(h_k) = ∫ h_k * g ∂μₙ (direct from hrep)
      have hphi_hk : (φ.comp extZ) (hhk_memLp.toLp h_k) = ∫ a, h_k a * g a ∂μₙ := by
        rw [hrep (hhk_memLp.toLp h_k)]
        apply integral_congr_ae
        filter_upwards [hhk_memLp.coeFn_toLp] with a ha; rw [ha]
      -- Pointwise: h_k(a) * g_k(a) ≤ h_k(a) * g(a)  (sign agreement)
      have hpw : ∀ a, h_k a * g_k a ≤ h_k a * g a := fun a => by
        suffices 0 ≤ h_k a * (g a - g_k a) by linarith [mul_sub (h_k a) (g a) (g_k a)]
        simp only [h_k, g_k]
        rcases le_or_gt (g a) (-(k : ℝ)) with h1 | h1
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = -(↑k : ℝ) :=
              max_eq_right (le_trans (min_le_left _ _) h1)
          rw [this]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [Real.sign_of_neg (neg_lt_zero.mpr (Nat.cast_pos.mpr hk))]
            exact mul_nonneg_of_nonpos_of_nonpos
              (mul_neg_of_neg_of_pos (by norm_num) (by positivity)) (by linarith)
        rcases le_or_gt (k : ℝ) (g a) with h2 | h2
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = (↑k : ℝ) :=
              by rw [min_eq_right h2, max_eq_left (neg_le_self (Nat.cast_nonneg k))]
          rw [this]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [Real.sign_of_pos (Nat.cast_pos.mpr hk)]
            exact mul_nonneg (mul_nonneg zero_le_one (by positivity)) (by linarith)
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = g a :=
              by rw [min_eq_left h2.le, max_eq_left (le_of_lt h1)]
          rw [this, sub_self, mul_zero]
      -- ∫ h_k * g_k = ‖g_k‖_q^q  (algebraic identity)
      have hgk_memLq : MemLp g_k q μₙ := by
        refine ⟨hgk_asm, ?_⟩
        calc eLpNorm g_k q μₙ
            ≤ eLpNorm (fun _ => (k : ℝ)) q μₙ := by
                apply eLpNorm_mono_ae
                exact ae_of_all μₙ fun a => by
                  simp [Real.norm_eq_abs]; exact hgk_bound a
          _ < ⊤ := eLpNorm_const_lt_top hq0' hqtop'
      have hint_hkgk : ∫ a, h_k a * g_k a ∂μₙ = (eLpNorm g_k q μₙ ^ q.toReal).toReal := by
        have hpw2 : ∀ a, h_k a * g_k a = |g_k a| ^ q.toReal := fun a => by
          simp only [h_k]
          have hsign : Real.sign (g_k a) * g_k a = |g_k a| := by
            rcases lt_trichotomy (g_k a) 0 with ha | rfl | ha
            · simp [Real.sign_neg ha, abs_of_neg ha]
            · simp
            · simp [Real.sign_pos ha, abs_of_pos ha]
          rw [show Real.sign (g_k a) * |g_k a| ^ (q.toReal - 1) * g_k a =
              |g_k a| ^ (q.toReal - 1) * (Real.sign (g_k a) * g_k a) from by ring,
              hsign, show |g_k a| = |g_k a| ^ (1 : ℝ) from (Real.rpow_one _).symm,
              ← Real.rpow_add (abs_nonneg _)]
          norm_num
        simp_rw [hpw2]
        have hpw3 : ∀ a, |g_k a| ^ q.toReal =
            ((‖g_k a‖₊ : ℝ≥0∞) ^ q.toReal).toReal := fun a => by
          rw [ENNReal.coe_rpow_of_nonneg (le_of_lt hq_pos'), ENNReal.coe_toReal, NNReal.coe_rpow]
          simp [Real.norm_eq_abs]
        simp_rw [hpw3]
        have hf_ne_top : ∀ᵐ a ∂μₙ, (‖g_k a‖₊ : ℝ≥0∞) ^ q.toReal ≠ ⊤ :=
          ae_of_all μₙ fun a => by
            rw [ENNReal.coe_rpow_of_nonneg (le_of_lt hq_pos')]; exact ENNReal.coe_ne_top
        rw [integral_toReal (hgk_asm.enorm.pow_const q.toReal) hf_ne_top]
        congr 1
        rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop', ← ENNReal.rpow_mul,
            one_div, inv_mul_cancel₀ hq_pos'.ne', ENNReal.rpow_one]
      -- ‖h_k‖_p = ‖g_k‖_q^(q/p)  (norm identity via hpq)
      have hpq_prod : p.toReal * q.toReal = p.toReal + q.toReal := by
        have h := hpq.inv_add_inv_eq_one
        field_simp [hp_pos'.ne', hq_pos'.ne'] at h; linarith
      have hn_eLpNorm : eLpNorm h_k p μₙ = eLpNorm g_k q μₙ ^ (q.toReal / p.toReal) := by
        have hpw_real : ∀ a, |h_k a| ^ p.toReal = |g_k a| ^ q.toReal := fun a => by
          simp only [h_k]
          rcases eq_or_ne (g_k a) 0 with ha | ha
          · simp [ha]
          · have habs_pos : 0 < |g_k a| := abs_pos.mpr ha
            have hsign1 : |Real.sign (g_k a)| = 1 := by
              rcases lt_trichotomy (g_k a) 0 with h | h | h
              · simp [Real.sign_neg h]
              · exact absurd h ha
              · simp [Real.sign_pos h]
            rw [abs_mul, hsign1, one_mul,
                abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
                ← Real.rpow_mul (abs_nonneg _)]
            congr 1; nlinarith [hpq_prod]
        have hpw_enn : ∀ a, (‖h_k a‖₊ : ℝ≥0∞) ^ p.toReal =
            (‖g_k a‖₊ : ℝ≥0∞) ^ q.toReal := fun a => by
          rw [ENNReal.coe_rpow_of_nonneg (le_of_lt hp_pos'),
              ENNReal.coe_rpow_of_nonneg (le_of_lt hq_pos')]
          norm_cast; apply NNReal.coe_injective
          simp only [NNReal.coe_rpow, NNReal.coe_nnnorm, Real.norm_eq_abs]
          exact hpw_real a
        rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop,
            eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop',
            lintegral_congr (fun a => hpw_enn a), ← ENNReal.rpow_mul]
        congr 1; field_simp [hp_pos'.ne', hq_pos'.ne']
      -- Assemble: ‖g_k‖_q^q ≤ ‖φ ∘ extZ‖ * ‖g_k‖_q^(q/p) → ‖g_k‖_q ≤ ‖φ ∘ extZ‖
      set x := (eLpNorm g_k q μₙ).toReal
      have hx_nn : 0 ≤ x := ENNReal.toReal_nonneg
      have hgk_ne_top : eLpNorm g_k q μₙ ≠ ⊤ := hgk_memLq.eLpNorm_lt_top.ne
      have hqp_eq : q.toReal / p.toReal + 1 = q.toReal := by
        field_simp [hp_pos'.ne']; linarith [hpq_prod]
      have hint_hkg_int : Integrable (fun a => h_k a * g_k a) μₙ :=
        integrable_mul_sf p q hpq (le_of_lt hp1) hptop hhk_memLp hgk_memLq
      have hint_hg_int : Integrable (fun a => h_k a * g a) μₙ :=
        integrable_mul_sf p q hpq (le_of_lt hp1) hptop hhk_memLp hg
      have hint_ineq : ∫ a, h_k a * g_k a ∂μₙ ≤ ∫ a, h_k a * g a ∂μₙ :=
        integral_mono hint_hkg_int hint_hg_int (fun a => hpw a)
      have hn_norm : ‖hhk_memLp.toLp h_k‖ = (eLpNorm h_k p μₙ).toReal := by
        simp only [Lp.norm_def]
        congr 1; exact eLpNorm_congr_ae hhk_memLp.coeFn_toLp
      have hchain : x ^ q.toReal ≤ ‖φ.comp extZ‖ * x ^ (q.toReal / p.toReal) := by
        have hlhs : x ^ q.toReal = (eLpNorm g_k q μₙ ^ q.toReal).toReal := by
          simp [x, ENNReal.toReal_rpow]
        have hrhs_eq : x ^ (q.toReal / p.toReal) = (eLpNorm h_k p μₙ).toReal := by
          rw [hn_eLpNorm, x, ENNReal.toReal_rpow]
        rw [hlhs, hrhs_eq]
        calc (eLpNorm g_k q μₙ ^ q.toReal).toReal
            = ∫ a, h_k a * g_k a ∂μₙ := hint_hkgk.symm
          _ ≤ ∫ a, h_k a * g a ∂μₙ := hint_ineq
          _ = (φ.comp extZ) (hhk_memLp.toLp h_k) := hphi_hk.symm
          _ ≤ ‖(φ.comp extZ) (hhk_memLp.toLp h_k)‖ := le_abs_self _
          _ ≤ ‖φ.comp extZ‖ * ‖hhk_memLp.toLp h_k‖ :=
                ContinuousLinearMap.le_opNorm _ _
          _ = ‖φ.comp extZ‖ * (eLpNorm h_k p μₙ).toReal := by rw [hn_norm]
      have hx_le : x ≤ ‖φ.comp extZ‖ := by
        rcases le_or_lt x 0 with hx | hx
        · linarith [norm_nonneg (φ.comp extZ)]
        · have hrpow : x ^ q.toReal = x ^ (q.toReal / p.toReal) * x := by
            conv_lhs =>
              rw [show q.toReal = q.toReal / p.toReal + 1 from by linarith [hqp_eq]]
            rw [Real.rpow_add hx, Real.rpow_one]
          have hxqp_pos : 0 < x ^ (q.toReal / p.toReal) := Real.rpow_pos_of_pos hx _
          have : x ^ (q.toReal / p.toReal) * x ≤ x ^ (q.toReal / p.toReal) * ‖φ.comp extZ‖ := by
            calc x ^ (q.toReal / p.toReal) * x
                = x ^ q.toReal := hrpow.symm
              _ ≤ ‖φ.comp extZ‖ * x ^ (q.toReal / p.toReal) := hchain
              _ = x ^ (q.toReal / p.toReal) * ‖φ.comp extZ‖ := mul_comm _ _
          exact le_of_mul_le_mul_left this hxqp_pos
      calc eLpNorm g_k q μₙ
          = ENNReal.ofReal x := (ENNReal.ofReal_toReal hgk_ne_top).symm
        _ ≤ ENNReal.ofReal ‖φ.comp extZ‖ := ENNReal.ofReal_le_ofReal hx_le
    -- MCT: eLpNorm g q μₙ ≤ ENNReal.ofReal ‖φ ∘ extZ‖ ≤ ENNReal.ofReal ‖φ‖
    apply le_trans _ (ENNReal.ofReal_le_ofReal hphin_le)
    rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop']
    -- ∫⁻ ‖g‖^q = ⨆_k ∫⁻ ‖g_k‖^q  (truncation MCT, mirrors rn_deriv_memLq_from_trunc)
    have hgn_lint : ∀ k : ℕ,
        ∫⁻ a, (‖(fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) a‖₊ : ℝ≥0∞) ^ q.toReal ∂μₙ ≤
        (ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal := fun k => by
      have h := htrunc k
      rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop'] at h
      calc ∫⁻ a, _ ∂μₙ
          = ((∫⁻ a, _ ∂μₙ) ^ (1 / q.toReal)) ^ q.toReal := by
              rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos'.ne', ENNReal.rpow_one]
        _ ≤ (ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal :=
              ENNReal.rpow_le_rpow h (le_of_lt hq_pos')
    have hMCT : ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μₙ =
        ⨆ k : ℕ, ∫⁻ a, (‖(fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) a‖₊ : ℝ≥0∞)
          ^ q.toReal ∂μₙ := by
      have abs_clamp : ∀ (r : ℝ) (k : ℕ), |max (min r k) (-(k : ℝ))| = min |r| k := by
        intro r k
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        rcases le_or_lt r (-(k : ℝ)) with h1 | h1
        · rw [min_eq_left (h1.trans (by linarith)), max_eq_right h1,
              abs_neg, abs_of_nonneg hk, abs_of_nonpos (h1.trans (by linarith)),
              min_eq_right (by linarith)]
        rcases le_or_lt (k : ℝ) r with h2 | h2
        · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hk,
              abs_of_nonneg (hk.trans h2), min_eq_right h2]
        · rw [min_eq_left h2.le, max_eq_left h1.le,
              min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
      have sup_min : ∀ (x : ℝ≥0∞), ⨆ k : ℕ, min x k = x := fun x => by
        rcases eq_or_ne x ⊤ with rfl | hx
        · simp [min_eq_right le_top, ENNReal.iSup_natCast]
        · apply le_antisymm (iSup_le fun k => min_le_left x k)
          obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hx
          exact (min_eq_left hK.le).symm ▸ le_iSup _ K
      have norm_gk_eq : ∀ (a : α) (k : ℕ),
          (‖max (min (g a) (k : ℝ)) (-(k : ℝ))‖₊ : ℝ≥0∞) = min (‖g a‖₊ : ℝ≥0∞) k := by
        intro a k; rw [← ENNReal.coe_min]; congr 1; apply NNReal.coe_injective
        push_cast [Real.norm_eq_abs]; exact abs_clamp (g a) k
      have ptwise_eq : ∀ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal =
          ⨆ k : ℕ, (min (‖g a‖₊ : ℝ≥0∞) k) ^ q.toReal := fun a => by
        rw [← sup_min (‖g a‖₊)]
        exact (ENNReal.orderIsoRpow q.toReal hq_pos').map_iSup _
      rw [show (fun a => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) =
          (fun a => ⨆ k : ℕ, (min (‖g a‖₊ : ℝ≥0∞) k) ^ q.toReal) from funext ptwise_eq,
          lintegral_iSup_ae
            (fun k => (hg.1.enorm.min aemeasurable_const).pow_const q.toReal)
            (ae_of_all μₙ fun a m k hmk => ENNReal.rpow_le_rpow
              (min_le_min_left _ (Nat.cast_le.mpr hmk)) (le_of_lt hq_pos'))]
      simp_rw [← norm_gk_eq]
    calc (∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μₙ) ^ (1 / q.toReal)
        ≤ ((ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal) ^ (1 / q.toReal) := by
            apply ENNReal.rpow_le_rpow _ (by positivity)
            rw [hMCT]; exact iSup_le hgn_lint
      _ = ENNReal.ofReal ‖φ.comp extZ‖ := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos'.ne', ENNReal.rpow_one]
  -- ── Step A2: Consistency ────────────────────────────────────────────────────
  -- g_seq m =ᵐ[μ.restrict Sₘ] g_seq n for m ≤ n, via set-integral uniqueness.
  -- Key: ∫_s gₘ ∂(μ.restrict Sₘ) = ∫_{s∩Sₘ} gₘ ∂μ = φ(1_{s∩Sₘ}) = ∫_{s∩Sₘ} gₙ ∂μ
  --    = ∫_s gₙ ∂(μ.restrict Sₘ)  [for all measurable s].
  have hconsist : ∀ m n : ℕ, m ≤ n →
      g_seq m =ᵐ[μ.restrict (spanningSets μ m)] g_seq n := by
    intro m n hmn
    haveI hfin_m : IsFiniteMeasure (μ.restrict (spanningSets μ m)) :=
      { measure_univ_lt_top := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_spanningSets_lt_top μ m }
    -- Integrability on (μ.restrict Sm) for both sides:
    -- 1 ≤ q from hpq.symm.one_lt_of_lt hp1 (same pattern as parent at line 885)
    have hq_ge1 : 1 ≤ q := by linarith [hpq.symm.one_lt_of_lt hp1]
    have hgm_int : Integrable (g_seq m) (μ.restrict (spanningSets μ m)) :=
      (hg_seq_mem m).integrable hq_ge1
    have hgn_small : MemLp (g_seq n) q (μ.restrict (spanningSets μ m)) :=
      (hg_seq_mem n).mono_measure (Measure.restrict_mono (spanningSets_mono μ hmn) le_rfl)
    have hgn_int : Integrable (g_seq n) (μ.restrict (spanningSets μ m)) :=
      hgn_small.integrable hq_ge1
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
        (fun s _ _ => hgm_int.integrableOn)
        (fun s _ _ => hgn_int.integrableOn)
    intro s hs _
    -- ∫_s f ∂(μ.restrict Sm) = ∫_{s ∩ Sm} f ∂μ  (Measure.restrict_restrict)
    have to_mu : ∀ f : α → ℝ,
        ∫ a in s, f a ∂(μ.restrict (spanningSets μ m)) =
        ∫ a in s ∩ spanningSets μ m, f a ∂μ := fun f => by
      rw [show (μ.restrict (spanningSets μ m)).restrict s = μ.restrict (s ∩ spanningSets μ m)
            from Measure.restrict_restrict (measurableSet_spanningSets μ m)]
    simp_rw [to_mu]
    have hfin_int : μ (s ∩ spanningSets μ m) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ m)).ne
    have hEn_m : s ∩ spanningSets μ m ⊆ spanningSets μ m := Set.inter_subset_right
    have hEn_n : s ∩ spanningSets μ m ⊆ spanningSets μ n :=
      hEn_m.trans (spanningSets_mono μ hmn)
    exact (hagree_n m _ (hs.inter (measurableSet_spanningSets μ m)) hEn_m hfin_int).symm.trans
          (hagree_n n _ (hs.inter (measurableSet_spanningSets μ m)) hEn_n hfin_int)
  -- ── Step A3: Construct global g ─────────────────────────────────────────────
  -- g(a) := g_seq n₀(a) a, where n₀(a) = first n with a ∈ Sₙ.
  -- By hconsist this is a.e. equal to g_seq n on every Sₙ.
  have hcover : ∀ a : α, ∃ n, a ∈ spanningSets μ n := fun a => by
    have := (iUnion_spanningSets μ).symm ▸ mem_univ a
    exact mem_iUnion.mp this
  let idx : α → ℕ := fun a => Nat.find (hcover a)
  let g : α → ℝ := fun a => g_seq (idx a) a
  -- ── Step A4: MemLp g q μ (via MCT + hgnorm) ─────────────────────────────────
  -- eLpNorm(g, q, μ)^q = ∫⁻ |g|^q dμ = ⨆_n ∫⁻_{Sₙ} |g|^q dμ [MCT, Sₙ ↑ univ]
  --                     = ⨆_n ∫⁻_{Sₙ} |g_seq n|^q dμ       [g = g_seq n a.e. on Sₙ]
  --                     ≤ ⨆_n ‖φ‖^q = ‖φ‖^q                 [by hgnorm]
  -- AEStronglyMeasurable g: each g_seq n is AEStronglyMeasurable on μ.restrict Sₙ;
  -- since Sₙ ↑ univ, g is AEStronglyMeasurable on μ.
  -- Derived constants needed below
  have hqtop : q ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
  have hq0 : q ≠ 0 := by
    intro h; rw [h, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hg_lq : MemLp g q μ := by
    -- Step 1: g =ᵐ[μ.restrict Sₙ] g_seq n for each n
    -- Proof: for each k ≤ n, hconsist gives g_seq k =ᵐ[μ.restrict Sₖ] g_seq n.
    -- For a.e. a ∈ Sₙ: g(a) = g_seq(idx a)(a) where idx a ≤ n, and
    -- g_seq(idx a)(a) = g_seq n(a) a.e. on S_{idx a} ⊆ Sₙ (finite union of null sets).
    have hg_eq_n : ∀ n, g =ᵐ[μ.restrict (spanningSets μ n)] g_seq n := by
      intro n
      rw [ae_restrict_iff' (measurableSet_spanningSets μ n), ae_iff]
      simp only [not_imp]
      -- For each k ≤ n, hconsist gives a null set on Sₖ where g_seq k ≠ g_seq n
      have hBk_null : ∀ k ≤ n, μ {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a} = 0 :=
        fun k hkn => by
          have h := ae_iff.mp
            ((ae_restrict_iff' (measurableSet_spanningSets μ k)).mp (hconsist k n hkn))
          convert h using 1; ext a; simp [not_imp]
      -- The biUnion over k = 0..n is null (finite union of null sets)
      have h_biUnion_null : μ (⋃ k ∈ Finset.range (n + 1),
          {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a}) = 0 :=
        le_antisymm
          (calc μ (⋃ k ∈ Finset.range (n + 1),
                  {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a})
              ≤ ∑ k ∈ Finset.range (n + 1),
                  μ {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a} :=
                measure_biUnion_finset_le _ _
            _ = 0 := Finset.sum_eq_zero fun k hk =>
                  hBk_null k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
          (zero_le _)
      -- Bad set {a ∈ Sₙ | g a ≠ g_seq n a} ⊆ biUnion (g(a) = g_seq(idx a)(a) definitionally)
      exact measure_mono_null
        (fun a ha => Set.mem_biUnion
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.find_min' (hcover a) ha.1)))
          ⟨Nat.find_spec (hcover a), ha.2⟩)
        h_biUnion_null
    -- Step 2: AEStronglyMeasurable g μ
    have hg_asm : AEStronglyMeasurable g μ :=
      aestronglyMeasurable_of_restrict_spanningSets μ fun n =>
        (hg_seq_mem n).1.congr_ae (hg_eq_n n).symm
    -- Step 3: eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖
    have hg_norm : eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
      apply ENNReal.rpow_le_rpow _ (by positivity)
      -- MCT: ∫⁻ ‖g‖^q dμ = ⨆_n ∫⁻_{Sₙ} ‖g‖^q dμ ≤ ⨆_n ‖φ‖^q = ‖φ‖^q
      have hbound_n : ∀ n,
          ∫⁻ a in spanningSets μ n, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
          (ENNReal.ofReal ‖φ‖) ^ q.toReal := fun n => by
        have heq : ∫⁻ a in spanningSets μ n, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ =
            ∫⁻ a, (‖g_seq n a‖₊ : ℝ≥0∞) ^ q.toReal ∂(μ.restrict (spanningSets μ n)) := by
          rw [lintegral_restrict_univ]
          apply lintegral_congr_ae
          filter_upwards [hg_eq_n n] with a ha
          simp [ha]
        rw [heq]
        have h := hgnorm n
        rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop] at h
        have h2 := ENNReal.rpow_le_rpow h (le_of_lt hq_pos)
        rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one] at h2
      -- lintegral over μ = ⨆_n lintegral over μ.restrict Sₙ (Beppo-Levi on spanning sets)
      have hMCT_global : ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ =
          ⨆ n, ∫⁻ a in spanningSets μ n, (‖g a‖₊ : ℝ≥0∞) ^ q.toReal ∂μ := by
        set f_ind : ℕ → α → ℝ≥0∞ := fun n a =>
            (spanningSets μ n).indicator (fun _ => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) a
        have hmeas_fn : ∀ n, AEMeasurable (f_ind n) μ := fun n =>
          ((hg_asm.enorm.pow_const q.toReal).indicator
            (measurableSet_spanningSets μ n))
        have hmono : ∀ᵐ a ∂μ, Monotone (fun n => f_ind n a) :=
          ae_of_all μ fun a m n hmn =>
            Set.indicator_le_indicator_of_subset (spanningSets_mono μ hmn) (fun _ => le_top) a
        have hptwise : ∀ a, ⨆ n, f_ind n a = (‖g a‖₊ : ℝ≥0∞) ^ q.toReal := fun a => by
          apply le_antisymm (iSup_le fun n => Set.indicator_le_self _ _ a)
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
            ((iUnion_spanningSets μ).symm ▸ Set.mem_univ a)
          exact le_iSup_of_le n (Set.indicator_of_mem hn _ ▸ le_refl _)
        rw [show (fun a => (‖g a‖₊ : ℝ≥0∞) ^ q.toReal) = fun a => ⨆ n, f_ind n a
              from funext (fun a => (hptwise a).symm),
            lintegral_iSup_ae hmeas_fn hmono]
        congr 1; ext n
        exact (lintegral_indicator (measurableSet_spanningSets μ n) _).symm
      rw [hMCT_global]
      exact iSup_le hbound_n
    exact ⟨hg_asm, (lt_of_le_of_lt hg_norm ENNReal.ofReal_lt_top).ne⟩
  -- ── Step A5: Indicator agreement for all E ───────────────────────────────────
  -- For E with μ(E) < ∞:
  --   φ(1_E) = lim_n φ(1_{E∩Sₙ})          [by lp_truncation_tendsto_zero + CLM continuity]
  --          = lim_n ∫_{E∩Sₙ} g dμ         [by hagree_n + g =ᵐ g_seq n on Sₙ]
  --          = ∫_E g dμ                     [by tendsto_setIntegral_of_monotone + DCT]
  refine ⟨g, hg_lq, ?_⟩
  intro E hE hfin
  -- Derived constant: q ≥ 1 (needed for Integrable from MemLp)
  have hq_ge1 : (1 : ℝ≥0∞) ≤ q :=
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal q.toReal :=
          ENNReal.ofReal_le_ofReal (hpq.symm.one_lt_of_lt hp1).le
      _ = q := ENNReal.ofReal_toReal hqtop
  -- Finite-measure helper for E ∩ Sₙ
  have hfin_n : ∀ n, μ (E ∩ spanningSets μ n) ≠ ⊤ := fun n =>
    ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  -- ── Step 1: φ(1_{E∩Sₙ}^Lp) = ∫_{E∩Sₙ} g dμ for each n ──────────────────────
  -- Use hagree_n (E ∩ Sₙ ⊆ Sₙ) to get ∫_{E∩Sₙ} g_seq n, then ae-equality on Sₙ
  have hphi_En : ∀ n,
      φ ((memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) 1
          (Or.inr (hfin_n n))).toLp _) =
      ∫ a in E ∩ spanningSets μ n, g a ∂μ := fun n => by
    rw [hagree_n n (E ∩ spanningSets μ n)
          (hE.inter (measurableSet_spanningSets μ n))
          Set.inter_subset_right (hfin_n n)]
    -- ∫_{E∩Sₙ} g_seq n = ∫_{E∩Sₙ} g  by hg_eq_n restricted to E ∩ Sₙ ⊆ Sₙ
    exact integral_congr_ae ((hg_eq_n n).filter_mono
      (Measure.ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl))).symm
  -- ── Step 2: ∫_{E∩Sₙ} g dμ → ∫_E g dμ  (monotone spanning-set convergence) ────
  have hUnion_E : (⋃ n, E ∩ spanningSets μ n) = E := by
    rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hg_int_E : Integrable g (μ.restrict (⋃ n, E ∩ spanningSets μ n)) := by
    rw [hUnion_E]
    exact (hg_lq.mono_measure (Measure.restrict_mono Set.subset_univ le_rfl)).integrable hq_ge1
  have htend_int : Tendsto (fun n => ∫ a in E ∩ spanningSets μ n, g a ∂μ)
      atTop (nhds (∫ a in E, g a ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone
      (fun n => hE.inter (measurableSet_spanningSets μ n))
      (fun m n hmn => Set.inter_subset_inter_right E (spanningSets_mono μ hmn))
      hg_int_E
    rwa [hUnion_E] at h
  -- ── Step 3: φ(1_{E∩Sₙ}^Lp) → φ(1_E^Lp)  (CLM continuity + Lp convergence) ───
  -- φ is bounded: |φ(h_n - h)| ≤ ‖φ‖ * ‖h_n - h‖.
  -- ‖h_n - h‖_Lp = (eLpNorm (1_{E∩Sₙ} - 1_E) p μ).toReal → 0
  -- via lp_truncation_tendsto_zero applied to 1_E (1_{E∩Sₙ} = 1_E * 1_{Sₙ}).
  set hind := indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop
  have htend_phi : Tendsto (fun n =>
      φ ((memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) 1
          (Or.inr (hfin_n n))).toLp _))
      atTop (nhds (φ (hind.toLp _))) := by
    -- SORRY: 1_{E∩Sₙ}^Lp → 1_E^Lp in Lp(μ), proved via:
    -- ‖h_n - h_Lp‖ = (eLpNorm (1_E - 1_E * 1_{Sₙ}) p μ).toReal (since 1_{E∩Sₙ} = 1_E * 1_{Sₙ})
    -- which → 0 by lp_truncation_tendsto_zero + ENNReal.tendsto_toReal.
    apply (φ.continuous.tendsto _).comp
    sorry
  -- ── Conclude by tendsto_nhds_unique ──────────────────────────────────────────
  -- Both φ(h_n) → φ(1_E) and φ(h_n) = ∫_{E∩Sₙ} g → ∫_E g, so the limits agree.
  have hseq_eq : (fun n => φ ((memLp_indicator_const p
        (hE.inter (measurableSet_spanningSets μ n)) 1 (Or.inr (hfin_n n))).toLp _)) =
      (fun n => ∫ a in E ∩ spanningSets μ n, g a ∂μ) := funext hphi_En
  exact (tendsto_nhds_unique (hseq_eq ▸ htend_phi) htend_int).symm

-- ============================================================================
-- § 6. Main theorem
-- ============================================================================

theorem riesz_lp_surjective_sigma_finite
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  obtain ⟨g, hg_lq, hagree⟩ := localization_existence p q hp1 hptop hpq φ
  refine ⟨g, hg_lq, ?_⟩
  apply integral_representation_sf p q hp1 hptop hpq φ g hg_lq
  intro E hE hfin
  have heq : (indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _ =
      (memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ := rfl
  rw [heq]
  exact hagree E hE hfin

end RieszSigmaFiniteComplete

end
