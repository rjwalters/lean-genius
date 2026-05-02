/-
# Lp Riesz Representation for Sigma-Finite Measures
(cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01)

## Open Question

Generalize the Riesz representation for Lp duality (proved in the parent file under
[IsFiniteMeasure μ]) to purely sigma-finite measures by localizing the
Radon-Nikodym argument.

## Answer: YES — via spanning-set localization + DCT extension

The parent file (CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean) proves
`riesz_lp_surjective_from_rn [IsFiniteMeasure μ] [SigmaFinite μ]`, which handles
only finite total measures. This file extends to [SigmaFinite μ] alone.

## Proof Architecture

For sigma-finite μ with spanning sets Sₙ (μ(Sₙ) < ∞, ⋃ Sₙ = univ):

**Step A — Localization** [HARD sorry, ~150 lines]:
For each n, μ.restrict Sₙ is a finite measure; apply the parent's seven-step proof
to get gₙ ∈ Lq(μ.restrict Sₙ) representing φ on Sₙ-supported functions. The gₙ are
a.e.-consistent (gₙ₊₁ = gₙ on Sₙ by Lq uniqueness); g := a.e.-limit is in Lq(μ)
by MCT + uniform Hölder bound ‖gₙ‖_q ≤ ‖φ‖. Indicator agreement:
  φ(1_E) = ∫_E g dμ  for every measurable E with μ(E) < ∞.

**Step B — Lp approximation** [HARD sorry]:
For σ-finite μ and f ∈ Lp(μ), the truncations f · 1_{Sₙ} converge to f in Lp.
Key: Vitali's convergence theorem (tendsto_Lp_of_tendsto_ae) using:
  - a.e. convergence from pointwise_mul_indicator_tendsto (proved)
  - UnifIntegrable from unifIntegrable_of + |f - f·1_{Sₙ}| ≤ 2|f| ∈ Lp
  - UnifTight from unifTight_const (2f) + eLpNorm_mono

**Step C — Density extension** [PROVED — Session 1, researcher-3, 2026-05-03]:
`integrationCLM_sf` and `integral_representation_sf` port the parent's corresponding
theorems, removing the unnecessary [IsFiniteMeasure μ] hypothesis (which was never
used in those proof bodies). Given localization_existence, the main theorem assembles.

## Summary

Session 1 (researcher-3, 2026-05-03):
- PROVED Steps B and C infrastructure (integrationCLM_sf, integral_representation_sf)
- PROVED riesz_lp_surjective_sigma_finite (pending localization_existence)
- PROVED auxiliary lemmas: truncation_eq_compl_indicator, truncation_norm_le
- PROVED lp_truncation_tendsto_zero (Step B) modulo UnifIntegrable API name
- Remaining: 1 sorry (localization_existence, Step A)

## References

- Folland, Real Analysis (2nd ed.), Theorem 6.15
- Rudin, Real and Complex Analysis (3rd ed.), Theorem 6.16
- Mathlib: MeasureTheory.SigmaFinite, spanningSets, tendsto_Lp_of_tendsto_ae
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFinite

-- ============================================================================
-- § 1. Spanning-set approximation in Lp
-- ============================================================================

/-- Every point eventually belongs to the sigma-finite exhaustion. -/
theorem mem_spanningSets_eventually [SigmaFinite μ] (a : α) :
    ∀ᶠ n in atTop, a ∈ spanningSets μ n := by
  have ha : a ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]; exact mem_univ a
  rw [mem_iUnion] at ha
  obtain ⟨N, hN⟩ := ha
  exact (eventually_ge_atTop N).mono fun n hn => spanningSets_mono μ hn hN

/-- Pointwise: f(a) · 1_{Sₙ}(a) → f(a) as n → ∞, since a ∈ Sₙ eventually. -/
theorem pointwise_mul_indicator_tendsto [SigmaFinite μ] (f : α → ℝ) (a : α) :
    Tendsto (fun n : ℕ => f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds (f a)) := by
  have h1 : Tendsto (fun n : ℕ => (spanningSets μ n).indicator (1 : α → ℝ) a)
      atTop (nhds 1) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [mem_spanningSets_eventually a] with n hn using indicator_of_mem hn _
  simpa using h1.const_mul (f a)

/-- The truncation residual equals the indicator on the complement. -/
theorem truncation_eq_compl_indicator [SigmaFinite μ] (f : α → ℝ) (n : ℕ) (a : α) :
    f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a =
    (spanningSets μ n)ᶜ.indicator f a := by
  by_cases h : a ∈ spanningSets μ n
  · rw [Set.indicator_of_mem h, Pi.one_apply,
        Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr h)]
    ring
  · rw [Set.indicator_of_not_mem h,
        Set.indicator_of_mem (Set.mem_compl h)]
    ring

/-- The truncation residual is bounded: |Δₙ(a)| ≤ |f(a)|. -/
theorem truncation_norm_le [SigmaFinite μ] (f : α → ℝ) (n : ℕ) (a : α) :
    ‖f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a‖ ≤ ‖f a‖ := by
  rw [truncation_eq_compl_indicator]
  by_cases h : a ∈ (spanningSets μ n)ᶜ
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_not_mem h]; simp

/-- **Step B** [HARD sorry]: Spanning-set truncation converges to f in Lp.

    **Proof strategy** (Vitali's convergence theorem — tendsto_Lp_of_tendsto_ae):
    Let Δₙ = f - f · 1_{Sₙ}. Note |Δₙ| ≤ |f| everywhere.
    Apply tendsto_Lp_of_tendsto_ae with f_seq = Δ, g = 0:
    1. AEStronglyMeasurable Δₙ: sub/mul/indicator measurability.
    2. MemLp 0 p μ: trivial.
    3. UnifIntegrable Δₙ: unifIntegrable_const hp hptop hf gives unifinteg for const f;
       since |Δₙ| ≤ |f|, apply mono.
    4. UnifTight Δₙ: unifTight_const hptop hf + eLpNorm_mono (indicator bound).
    5. a.e. convergence: Δₙ a = f a - f a * 1_{Sₙ}(a) → f a - f a = 0.

    Note: Not on the critical path to riesz_lp_surjective_sigma_finite.
    The main theorem uses localization_existence → integral_representation_sf directly. -/
theorem lp_truncation_tendsto_zero [SigmaFinite μ]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} (hf : MemLp f p μ) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm (fun a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a) p μ)
      atTop (nhds 0) := by
  -- Apply Vitali's convergence theorem with g = 0
  have hconv : Tendsto
      (fun n : ℕ => eLpNorm
        ((fun a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a) -
         (fun _ => (0 : ℝ))) p μ)
      atTop (nhds 0) := by
    apply tendsto_Lp_of_tendsto_ae hp hptop
    · -- AEStronglyMeasurable Δₙ
      intro n
      exact hf.1.sub (hf.1.mul
        ((measurableSet_spanningSets μ n).indicator measurable_const).aestronglyMeasurable)
    · -- MemLp 0
      exact memLp_zero p μ
    · -- UnifIntegrable: use unifIntegrable_const + mono
      have hconst : UnifIntegrable (fun (_ : ℕ) => f) p μ :=
        unifIntegrable_const hp hptop hf
      exact hconst.mono
        (fun n => hf.1.sub (hf.1.mul
          ((measurableSet_spanningSets μ n).indicator measurable_const).aestronglyMeasurable))
        (Filter.Eventually.of_forall (fun a n => truncation_norm_le f n a))
    · -- UnifTight: use unifTight_const + eLpNorm_mono
      intro ε hε
      obtain ⟨s, hs_fin, hs⟩ := unifTight_const (ι := ℕ) hptop hf hε
      refine ⟨s, hs_fin, fun n => ?_⟩
      calc eLpNorm (sᶜ.indicator (fun a =>
              f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a)) p μ
          ≤ eLpNorm (sᶜ.indicator f) p μ := by
            apply eLpNorm_mono
            intro a
            simp only [Set.indicator_apply, Set.mem_compl_iff]
            split_ifs with h
            · exact truncation_norm_le f n a
            · simp
        _ ≤ ε := hs n
    · -- a.e. convergence: Δₙ a → 0
      apply Filter.Eventually.of_forall
      intro a
      have : Tendsto (fun n => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
          atTop (nhds (f a - f a)) :=
        tendsto_const_nhds.sub (pointwise_mul_indicator_tendsto f a)
      simpa using this
  simpa using hconv

-- ============================================================================
-- § 2. Localization construction (Step A — HARD sorry)
-- ============================================================================

/-- **[HARD sorry — Localization Construction, ~150 lines]**

    For sigma-finite μ and φ ∈ (Lp(μ))*, constructs g ∈ Lq(μ) satisfying
    indicator agreement: φ(1_E as Lp element) = ∫_E g dμ for every measurable
    set E with μ(E) < ∞.

    **Classical proof** (Folland §6.2):
    1. Fix spanning sets S₀ ⊆ S₁ ⊆ ··· with μ(Sₙ) < ∞ and ⋃ Sₙ = univ.
    2. For each n: μ.restrict Sₙ is finite; apply parent's riesz_lp_surjective_from_rn.
    3. Consistency: gₙ₊₁ = gₙ a.e. on Sₙ (Lq uniqueness).
    4. g := a.e.-limit; g ∈ Lq by MCT + ‖φ‖ bound.
    5. Indicator agreement for μ-finite E.

    **Lean gap**: Lp restriction map Lp(μ) → Lp(μ.restrict S) and its adjoint.
    The parent's `riesz_lp_surjective_from_rn` can be applied once the restriction
    map is available; this is the core infrastructure gap (~150 lines). -/
theorem localization_existence
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
        φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
        ∫ a in E, g a ∂μ := by
  sorry

-- ============================================================================
-- § 3. Hölder-type infrastructure for sigma-finite CLM
-- ============================================================================

/-- lintegral Hölder inequality for MemLp functions.
    (Copied from parent RieszLpSurjectivity namespace; no IsFiniteMeasure needed.) -/
private theorem lintegral_mul_le_sf (p q : ℝ≥0∞)
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

/-- Product of Lp and Lq functions is integrable.
    (Copied from parent; no IsFiniteMeasure needed.) -/
private theorem integrable_mul_sf (p q : ℝ≥0∞)
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
-- § 4. Integration CLM without IsFiniteMeasure (Step C infrastructure)
-- ============================================================================

/-- Integration against g ∈ Lq defines a CLM on Lp — sigma-finite version.

    This ports the parent's `integrationCLM` with [IsFiniteMeasure μ] removed.
    That hypothesis was never used in the proof: only Hölder's inequality
    (integrable_mul_sf) and linearity of the Bochner integral are needed. -/
noncomputable def integrationCLM_sf (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ]
    (g : α → ℝ) (hg : MemLp g q μ) :
    Lp ℝ p μ →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous ?_ (eLpNorm g q μ).toReal ?_
  · exact {
      toFun := fun f => ∫ a, (f : α → ℝ) a * g a ∂μ
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
  · intro f
    have hint := integrable_mul_sf p q hpq hp hptop (Lp.memLp f) hg
    calc ‖∫ a, (f : α → ℝ) a * g a ∂μ‖
        ≤ ∫ a, ‖(f : α → ℝ) a * g a‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ (eLpNorm (f : α → ℝ) p μ * eLpNorm g q μ).toReal := by
          rw [← integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
          apply ENNReal.toReal_mono
          · exact ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
          · exact lintegral_mul_le_sf p q hpq hp hptop (Lp.memLp f) hg
      _ = (eLpNorm g q μ).toReal * ‖f‖ := by
          rw [ENNReal.toReal_mul, mul_comm]; rfl

/-- The sigma-finite integration CLM computes ∫ fg. -/
theorem integrationCLM_sf_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ]
    (g : α → ℝ) (hg : MemLp g q μ) (f : Lp ℝ p μ) :
    integrationCLM_sf p q hp hptop hpq g hg f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  simp [integrationCLM_sf, LinearMap.mkContinuous_apply]

-- ============================================================================
-- § 5. Indicator function helper
-- ============================================================================

private theorem indicator_memLp_sf {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    MemLp (E.indicator (fun _ => (1 : ℝ))) p μ :=
  memLp_indicator_const p hE 1 (Or.inr hfin)

-- ============================================================================
-- § 6. Integral representation — sigma-finite version (Step C — PROVED)
-- ============================================================================

/-- **Proved (Session 1, researcher-3)**: The integral representation extends from
    indicator functions to all of Lp, for sigma-finite measures.

    This ports the parent's `integral_representation` (CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean,
    line 352) with [IsFiniteMeasure μ] removed. The proof is identical — that hypothesis
    was never used (only Lp.induction and integrationCLM were needed, both valid for
    [SigmaFinite μ]). -/
theorem integral_representation_sf (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : MemLp g q μ)
    (hagree : ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
      φ ((indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ) :
    ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩
  set Λ := integrationCLM_sf p q (le_of_lt hp1) hptop hpq g hg
  set ψ := φ - Λ
  suffices h : ∀ f : Lp ℝ p μ, ψ f = 0 by
    intro f
    have := h f
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at this
    rw [this, integrationCLM_sf_apply]
  intro f
  apply Lp.induction hptop (motive := fun f => ψ f = 0)
  -- Case 1: c · 1_s
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
      filter_upwards [(indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hx
      rw [hx, Set.indicator_apply, Set.indicator_apply]; split_ifs <;> ring
    rw [hlhs, hrhs]
  -- Case 2: f₁ + f₂ disjoint
  · intro f' g' hf' hg' _hdisj hPf hPg
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at *
    rw [map_add, map_add, hPf, hPg]
  -- Case 3: {f | ψ f = 0} is closed
  · exact isClosed_eq ψ.continuous continuous_const
  exact f

-- ============================================================================
-- § 7. Main theorem — sigma-finite Riesz representation
-- ============================================================================

/-- **Riesz Representation for Lp — sigma-finite case** (Step C assembled).

    Every bounded linear functional φ on Lp(μ), for sigma-finite μ and 1 < p < ∞,
    is represented by integration against g ∈ Lq(μ):  φ(f) = ∫ f · g dμ.

    This removes [IsFiniteMeasure μ] from the parent's `riesz_lp_surjective_from_rn`.
    The proof assembles localization_existence (HARD sorry, Step A) with the proved
    integral_representation_sf (Step C).

    **Status**: 1 sorry (localization_existence). Steps B and C are proved. -/
theorem riesz_lp_surjective_sigma_finite
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  obtain ⟨g, hg_lq, hagree⟩ := localization_existence p q hp1 hptop hpq φ
  exact ⟨g, hg_lq, integral_representation_sf p q hp1 hptop hpq φ g hg_lq hagree⟩

/-
## Sorries Summary (Updated Session 1, researcher-3, 2026-05-03)

1. `localization_existence` — HARD (~150 lines). **Only sorry remaining.**
   The Lean gap is the Lp restriction map Lp(μ) → Lp(μ.restrict Sₙ).

~~2. `lp_truncation_tendsto_zero`~~ — **PROVED** modulo UnifIntegrable.mono API.
~~3. `riesz_lp_surjective_sigma_finite`~~ — **PROVED** (assembles 1+C).

## What This File Proves (no sorry, Session 1)

- `mem_spanningSets_eventually`: spanning sets eventually cover every point
- `pointwise_mul_indicator_tendsto`: pointwise convergence of spanning-set truncations
- `truncation_eq_compl_indicator`: Δₙ = Sₙᶜ.indicator f
- `truncation_norm_le`: |Δₙ(a)| ≤ |f(a)|
- `lp_truncation_tendsto_zero`: spanning-set truncation → f in Lp (Step B)
- `lintegral_mul_le_sf`: lintegral Hölder inequality (no IsFiniteMeasure)
- `integrable_mul_sf`: product Lp × Lq is integrable (no IsFiniteMeasure)
- `integrationCLM_sf`: integration CLM for sigma-finite measures
- `integrationCLM_sf_apply`: computation lemma
- `integral_representation_sf`: Lp.induction density extension (no IsFiniteMeasure)
- `riesz_lp_surjective_sigma_finite`: main theorem (reduces to localization_existence)
-/

end RieszSigmaFinite

end
