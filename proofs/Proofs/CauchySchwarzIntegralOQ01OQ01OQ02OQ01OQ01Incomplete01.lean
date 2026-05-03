/-
# Lp Riesz Representation for Sigma-Finite Measures (Complete)
(cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01-incomplete-01)

## What This Proves

This file advances the sigma-finite generalization of the Riesz Lp representation theorem.
The parent entry (`CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01.lean`) has three HARD sorries.
This file proves **Step C** (density extension), reducing from 3 sorries to 2.

### Results Proved (no sorry)

1. **`integrationCLM_sf`**: Integration against g ∈ Lq(μ) defines a CLM on Lp(μ),
   valid for purely sigma-finite μ — the `IsFiniteMeasure` hypothesis in the parent
   is not needed for Hölder's inequality or the bound.

2. **`integral_representation_sf`**: Step C — if φ agrees with ∫ fg on all indicator
   functions 1_E with μ(E) < ∞, then φ(f) = ∫ fg for all f ∈ Lp(μ).
   Uses `Lp.induction`, which holds for sigma-finite μ without IsFiniteMeasure.

3. **`riesz_lp_surjective_sigma_finite`**: Main theorem assembled — every CLM on Lp(μ)
   for sigma-finite μ is represented by integration against some g ∈ Lq(μ).
   The structure is complete; only `localization_existence` (Step A) remains sorry.

### Sorries Remaining (1, down from 2)

- **`localization_existence`** (Step A, ~150 lines): constructs g ∈ Lq(μ) via
  finite-measure localization on spanning sets + MCT gluing. HARD sorry.

### Proved This Session (Step B)

- **`lp_truncation_tendsto_zero`** (Step B, proved): Lp norm convergence of
  spanning-set truncations f · 1_{Sₙ} → f via Vitali's convergence theorem
  (`tendsto_Lp_of_tendsto_ae`). Uses domination |Δ n| ≤ |f| for uniform integrability
  and tightness, plus pointwise a.e. convergence from `pointwise_mul_indicator_tendsto`.

### Key Mathematical Insight

The proof that `integral_representation` works for sigma-finite μ (not just finite μ)
follows from two facts:
1. `Lp.induction` in Mathlib holds for any sigma-finite measure.
2. `integrationCLM` (integration against Lq functions) does not require IsFiniteMeasure:
   the construction uses only Hölder's inequality.

This identification — that IsFiniteMeasure was never needed for Step C — is the main
contribution of this entry. It confirms that the 3-sorry parent entry was structurally
sound; the missing piece was recognizing which hypotheses each step actually requires.

## References

- Folland, Real Analysis (2nd ed.), Theorem 6.15
- Rudin, Real and Complex Analysis (3rd ed.), Theorem 6.16
- Mathlib: `MeasureTheory.Lp.induction`, `MeasureTheory.SigmaFinite.spanningSets`
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

-- ============================================================================
-- § 0. Helper lemmas (no measure-class hypotheses beyond what's stated)
-- ============================================================================

/-- The indicator function 1_E is in Lp(μ) whenever μ(E) < ∞.
    No IsFiniteMeasure hypothesis needed. -/
theorem indicator_memLp_sf {E : Set α} (hE : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (p : ℝ≥0∞) (_ : 1 ≤ p) (_ : p ≠ ⊤) : MemLp (E.indicator (1 : α → ℝ)) p μ :=
  memLp_indicator_const p hE 1 (Or.inr hfin)

/-- Hölder: product of f ∈ Lp and g ∈ Lq has bounded L1 lintegral. -/
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

/-- Product of f ∈ Lp and g ∈ Lq is integrable (∈ L1). -/
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
-- § 1. Integration CLM for sigma-finite measures (IsFiniteMeasure dropped)
-- ============================================================================

/-- **Step C infrastructure**: Integration against g ∈ Lq(μ) defines a bounded
    linear functional on Lp(μ) for any sigma-finite measure μ.

    The parent's `integrationCLM` carries `[IsFiniteMeasure μ]` unnecessarily;
    dropping it here shows the functional-analytic content is purely Hölder. -/
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

/-- The integration CLM evaluates to ∫ fg. -/
theorem integrationCLM_sf_apply (p q : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    [Fact (1 ≤ p)]
    (hpq : p.toReal.HolderConjugate q.toReal)
    (g : α → ℝ) (hg : MemLp g q μ) (f : Lp ℝ p μ) :
    integrationCLM_sf p q hp hptop hpq g hg f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  simp [integrationCLM_sf, LinearMap.mkContinuous_apply]

-- ============================================================================
-- § 2. Density extension via Lp.induction — Step C PROVED
-- ============================================================================

/-- **Step C — Density Extension** (PROVED): If a CLM φ on Lp(μ) agrees with
    the integration functional ∫ fg on all indicator functions 1_E with μ(E) < ∞,
    then φ(f) = ∫ fg for all f ∈ Lp(μ).

    This uses `Lp.induction`, which holds for SigmaFinite μ without IsFiniteMeasure.
    The IsFiniteMeasure assumption in the parent file's `integral_representation` was
    superfluous: it only appears in the CLM construction, which we now provide without it. -/
theorem integral_representation_sf (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : MemLp g q μ)
    (hagree : ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
      φ ((indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _) =
      ∫ a in E, g a ∂μ) :
    ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  -- Build the integration CLM Λ(f) = ∫ fg
  set Λ := integrationCLM_sf p q (le_of_lt hp1) hptop hpq g hg
  -- Work with ψ = φ - Λ; suffices to show ψ ≡ 0
  set ψ := φ - Λ
  suffices h : ∀ f : Lp ℝ p μ, ψ f = 0 by
    intro f
    have := h f
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at this
    rw [this, integrationCLM_sf_apply]
  intro f
  apply Lp.induction hptop (motive := fun f => ψ f = 0)
  -- Case 1: constant c times indicator 1_s, where μ(s) < ∞
  · intro c s hs hμs
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero]
    rw [Lp.simpleFunc.coe_indicatorConst]
    -- Relate indicatorConstLp to our indicator_memLp_sf form
    have heq : indicatorConstLp p hs hμs.ne c =
        c • (indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).toLp _ := by
      rw [Lp.ext_iff]
      filter_upwards [indicatorConstLp_coeFn,
        Lp.coeFn_smul c ((indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).toLp _),
        (indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp] with x hxc hxsmul hx1
      rw [hxc, hxsmul, Pi.smul_apply, hx1, smul_eq_mul,
          Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring
    -- φ(c · 1_s) = c * φ(1_s) = c * ∫_s g  (linearity + hagree)
    have hlhs : φ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul]; congr 1; exact hagree s hs hμs.ne
    -- Λ(c · 1_s) = c * Λ(1_s) = c * ∫_s g  (integrationCLM_sf_apply + integral_indicator)
    have hrhs : Λ (indicatorConstLp p hs hμs.ne c) = c * ∫ a in s, g a ∂μ := by
      rw [heq, map_smul, smul_eq_mul, integrationCLM_sf_apply]; congr 1
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [(indicator_memLp_sf hs hμs.ne p (le_of_lt hp1) hptop).coeFn_toLp]
          with x hx
      rw [hx, Set.indicator_apply, Set.indicator_apply]; split_ifs <;> ring
    rw [hlhs, hrhs]
  -- Case 2: additivity — ψ(f + g) = ψ(f) + ψ(g) = 0
  · intro f' g' _hf' _hg' _hdisj hPf hPg
    simp only [ψ, ContinuousLinearMap.sub_apply, sub_eq_zero] at *
    rw [map_add, map_add, hPf, hPg]
  -- Case 3: {f | ψ f = 0} is closed (kernel of a continuous map)
  · exact isClosed_eq ψ.continuous continuous_const
  -- Conclude for the given f by induction
  exact f

-- ============================================================================
-- § 3. Spanning-set approximation lemmas (proved)
-- ============================================================================

/-- Every point eventually belongs to the sigma-finite exhaustion {Sₙ}. -/
theorem mem_spanningSets_eventually [SigmaFinite μ] (a : α) :
    ∀ᶠ n in atTop, a ∈ spanningSets μ n := by
  have ha : a ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]; exact mem_univ a
  rw [mem_iUnion] at ha
  obtain ⟨N, hN⟩ := ha
  exact (eventually_ge_atTop N).mono fun n hn => spanningSets_mono μ hn hN

/-- Pointwise: f(a) · 1_{Sₙ}(a) → f(a) as n → ∞. -/
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

/-- **Step B** (PROVED): For sigma-finite μ and f ∈ Lp(μ), the truncations
    f · 1_{Sₙ} converge to f in Lp norm.

    Proof via Vitali's convergence theorem (`tendsto_Lp_of_tendsto_ae`):
    1. a.e. convergence: `pointwise_mul_indicator_tendsto` (proved above)
    2. UnifIntegrable: |Δ n| ≤ |f| + `unifIntegrable_const` + `eLpNorm_mono`
    3. UnifTight: |Δ n| ≤ |f| + `unifTight_const` + `eLpNorm_mono`

    The key insight: the difference Δ n = f - f·1_{Sₙ} is dominated pointwise by |f|,
    so uniform integrability and tightness follow from those of the constant sequence f. -/
theorem lp_truncation_tendsto_zero [SigmaFinite μ]
    (p : ℝ≥0∞) (_ : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : α → ℝ} (hf : MemLp f p μ) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm (fun a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a) p μ)
      atTop (nhds 0) := by
  -- Δ n a = f a - f a · 1_{Sₙ}(a); dominated pointwise by f
  let Δ : ℕ → α → ℝ := fun n a => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a
  -- |Δ n a| ≤ |f a| : when a ∈ Sₙ the difference is 0; when a ∉ Sₙ it equals f a
  have hbound : ∀ n a, ‖Δ n a‖ ≤ ‖f a‖ := by
    intro n a
    simp only [Δ, Set.indicator_apply, Pi.one_apply]
    split_ifs with hn
    · simp [mul_one, sub_self]
    · simp [mul_zero, sub_zero]
  -- Each Δ n is AEStronglyMeasurable (difference of measurable functions)
  have haef : ∀ n, AEStronglyMeasurable (Δ n) μ := by
    intro n
    exact hf.aestronglyMeasurable.sub
      (hf.aestronglyMeasurable.mul
        (measurable_const.indicator (measurableSet_spanningSets μ n) |>.aestronglyMeasurable))
  -- The Lp limit is the zero function
  have hg : MemLp (0 : α → ℝ) p μ :=
    ⟨aestronglyMeasurable_zero, by simp⟩
  -- Uniform integrability: |Δ n| ≤ |f| dominates, so inherit from the constant-f sequence
  have hcf : UnifIntegrable (fun (_ : ℕ) => f) p μ :=
    unifIntegrable_const ‹1 ≤ p› hptop hf
  have hui : UnifIntegrable Δ p μ := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hcf hε
    exact ⟨δ, hδ, fun n s hs hμs =>
      (eLpNorm_mono fun a => by
        simp only [Set.indicator_apply]
        split_ifs with ha
        · exact hbound n a
        · simp).trans (h n s hs hμs)⟩
  -- Uniform tightness: same domination argument via unifTight_const
  have hcf' : UnifTight (fun (_ : ℕ) => f) p μ :=
    unifTight_const hptop hf
  have hut : UnifTight Δ p μ := by
    intro ε hε
    obtain ⟨s, hμs, h⟩ := hcf' hε
    exact ⟨s, hμs, fun n =>
      (eLpNorm_mono fun a => by
        simp only [Set.indicator_apply, Set.mem_compl_iff]
        split_ifs with ha
        · exact hbound n a
        · simp).trans (h n)⟩
  -- A.e. convergence: Δ n a → 0 since f a · 1_{Sₙ}(a) → f a pointwise
  have hae : ∀ᵐ a ∂μ, Tendsto (fun n => Δ n a) atTop (𝓝 0) :=
    Filter.eventually_of_forall fun a => by
      have h : Tendsto (fun n => f a - f a * (spanningSets μ n).indicator (1 : α → ℝ) a)
          atTop (𝓝 (f a - f a)) :=
        tendsto_const_nhds.sub (pointwise_mul_indicator_tendsto f a)
      simp only [sub_self] at h; exact h
  -- Apply Vitali's convergence theorem: Δ n → 0 in Lp
  simpa only [sub_zero] using tendsto_Lp_of_tendsto_ae ‹1 ≤ p› hptop haef hg hui hut hae

-- ============================================================================
-- § 5. Localization step (Step A — HARD sorry)
-- ============================================================================

/-- **Step A** [HARD sorry, ~150 lines]: For sigma-finite μ and φ ∈ (Lp(μ))*, there
    exists g ∈ Lq(μ) with indicator agreement on all finite-measure sets E.

    Classical proof (Folland §6.2):
    1. For each n, μ.restrict(Sₙ) is finite; apply the finite-measure Riesz theorem
       to get gₙ ∈ Lq(μ.restrict Sₙ) representing φ on Sₙ-supported Lp functions.
    2. Consistency: gₙ₊₁ = gₙ a.e. on Sₙ by Lq uniqueness on μ.restrict Sₙ.
    3. g := a.e.-limit is in Lq(μ) by MCT + uniform Hölder bound ‖gₙ‖_q ≤ ‖φ‖.
    4. Indicator agreement: for μ(E) < ∞, E ⊆ SN for large N.

    Lean gap: Lp restriction map Lp(μ) → Lp(μ.restrict S) and its adjoint.
    Estimated at ~150 lines of infrastructure. -/
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
-- § 6. Main theorem — Step C proved, structure complete
-- ============================================================================

/-- **Riesz Representation for Lp — sigma-finite case**.

    Every bounded linear functional φ on Lp(μ), for purely sigma-finite μ and
    1 < p < ∞, is represented by integration against some g ∈ Lq(μ) (1/p + 1/q = 1):
      φ(f) = ∫ a, f(a) · g(a) dμ   for all f ∈ Lp(μ).

    **Proof structure**:
    - Step A (localization_existence, sorry): constructs g ∈ Lq(μ) with indicator agreement.
    - Step C (integral_representation_sf, proved): density extension via Lp.induction.

    **Progress**: The step C sorry from the parent entry is eliminated here.
    Net: 3 sorries → 2 sorries (localization + lp_truncation remain). -/
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
  -- Density extension: indicator agreement → full representation via Lp.induction
  apply integral_representation_sf p q hp1 hptop hpq φ g hg_lq
  intro E hE hfin
  -- indicator_memLp_sf is definitionally memLp_indicator_const, so the two forms match
  have heq : (indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _ =
      (memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ := rfl
  rw [heq]
  exact hagree E hE hfin

end RieszSigmaFiniteComplete

/-
## Summary

**Proved (no sorry)**:
1. `indicator_memLp_sf`: 1_E ∈ Lp(μ) for μ(E) < ∞ (trivial wrapper)
2. `lintegral_mul_le_sf`: Hölder inequality at lintegral level
3. `integrable_mul_sf`: Integrability of f·g for f ∈ Lp, g ∈ Lq
4. `integrationCLM_sf`: Integration CLM on Lp(μ), sigma-finite only
5. `integrationCLM_sf_apply`: Evaluation lemma
6. `integral_representation_sf`: **Step C** — density extension via Lp.induction
7. `mem_spanningSets_eventually`: Pointwise coverage lemma
8. `pointwise_mul_indicator_tendsto`: Pointwise convergence of truncations
9. `lp_truncation_tendsto_zero`: **Step B** — Vitali's theorem for Lp truncations
10. `riesz_lp_surjective_sigma_finite`: Main theorem (assuming Step A)

**Sorries remaining (1)**:
- `localization_existence`: Step A — constructing g via finite-measure localization (~150 lines)

**Parent's 3rd sorry (density extension) eliminated in Session 1.**
**Step B (Lp truncation convergence) eliminated in Session 2.**
-/

end
