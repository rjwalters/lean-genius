/-
# The Lp Restriction Map and the Splitting of Extension-by-Zero
(cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01-incomplete-01-oq-01)

## What This Proves

The σ-finite Lp Riesz representation development localizes a functional on `Lp(μ)`
to each set `S` of a spanning σ-finite cover using the **extension-by-zero** map

  `extByZeroCLM : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ`,   `g ↦ [S.indicator g]`.

The parent open question `oq-01` asked whether the *restriction* map
`Lp(μ) → Lp(μ.restrict S)` could instead serve as the localization device.  The
parent's answer was "yes in principle, but `extByZeroCLM` sufficed, so the
restriction map was never built."

This file constructs that missing companion map and proves it is a genuine
**left inverse** (retraction) of extension-by-zero.  Together, the two maps
exhibit `Lp(μ.restrict S)` as an isometrically embedded, norm-`1`-retracted
(hence `1`-complemented) subspace of `Lp(μ)`.

### Results Proved (no sorry, no axiom)

1. `extByZeroCLM` — extension-by-zero isometry `Lp(μ.restrict S) →L[ℝ] Lp(μ)`
   (self-contained restatement, so the file verifies against Mathlib alone).
2. `restrictToLpCLM` — the restriction map `Lp(μ) →L[ℝ] Lp(μ.restrict S)`,
   a norm-nonincreasing CLM.
3. `restrictToLpCLM_coeFn` — `⇑(restrictToLpCLM S f) =ᵐ[μ.restrict S] ⇑f`.
4. `restrictToLpCLM_norm_apply_le` / `restrictToLpCLM_opNorm_le_one`
   — `‖restrictToLpCLM S f‖ ≤ ‖f‖` and `‖restrictToLpCLM S‖ ≤ 1`.
5. `restrictToLpCLM_extByZeroCLM` — **the retraction identity**
   `restrictToLpCLM S (extByZeroCLM hS hp hptop g) = g`.
6. `restrictToLpCLM_comp_extByZeroCLM` — the composed CLM is the identity.
7. `extByZeroCLM_injective` — immediate corollary: extension-by-zero is injective.

## References

- Folland, Real Analysis (2nd ed.), §6.2 (Lp duality, σ-finite localization).
- Mathlib: `MeasureTheory.MemLp.restrict`, `MeasureTheory.eLpNorm_restrict_le`,
  `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`,
  `MeasureTheory.ae_restrict_of_ae`, `MeasureTheory.ae_restrict_mem`.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

-- ============================================================================
-- § 1. Extension-by-zero  Lp(μ.restrict S) →L[ℝ] Lp(μ)  (self-contained)
-- ============================================================================

/-- If `f ∈ Lp(μ.restrict S)`, then `S.indicator f ∈ Lp(μ)`.  The `eLpNorm` is
literally preserved, via Mathlib's `eLpNorm_indicator_eq_eLpNorm_restrict`. -/
private theorem memLp_indicator_of_restrict {S : Set α} (hS : MeasurableSet S)
    {f : α → ℝ} {p : ℝ≥0∞} (hf : MemLp f p (μ.restrict S)) :
    MemLp (S.indicator f) p μ := by
  refine ⟨(aestronglyMeasurable_indicator_iff hS).mpr hf.1, ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]
  exact hf.2

/-- **Extension-by-zero:** the isometric embedding `Lp(μ.restrict S) →L[ℝ] Lp(μ)`
sending a class `g` to the class of `S.indicator g`. -/
noncomputable def extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_indicator_of_restrict hS (Lp.memLp f)).toLp _
      map_add' := fun f₁ f₂ => by
        rw [Lp.ext_iff]
        filter_upwards [
          (memLp_indicator_of_restrict hS (Lp.memLp (f₁ + f₂))).coeFn_toLp,
          (memLp_indicator_of_restrict hS (Lp.memLp f₁)).coeFn_toLp,
          (memLp_indicator_of_restrict hS (Lp.memLp f₂)).coeFn_toLp,
          Lp.coeFn_add ((memLp_indicator_of_restrict hS (Lp.memLp f₁)).toLp _)
            ((memLp_indicator_of_restrict hS (Lp.memLp f₂)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        rw [h12, hadd]
        simp only [Pi.add_apply, h1, h2]
        by_cases ha : a ∈ S
        · simp only [Set.indicator_of_mem ha]; simpa using hinner ha
        · simp only [Set.indicator_of_notMem ha, add_zero]
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [
          (memLp_indicator_of_restrict hS (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_indicator_of_restrict hS (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_indicator_of_restrict hS (Lp.memLp f)).toLp _),
          (ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        rw [hcf, RingHom.id_apply, hsmul]
        simp only [Pi.smul_apply, hf, smul_eq_mul]
        by_cases ha : a ∈ S
        · simp only [Set.indicator_of_mem ha]; rw [hinner ha]; simp
        · simp only [Set.indicator_of_notMem ha, mul_zero] }
    1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have heq : ‖(memLp_indicator_of_restrict hS (Lp.memLp f)).toLp _‖ = ‖f‖ := by
        simp only [Lp.norm_def]
        congr 1
        rw [eLpNorm_congr_ae (memLp_indicator_of_restrict hS (Lp.memLp f)).coeFn_toLp,
            eLpNorm_indicator_eq_eLpNorm_restrict hS]
      exact heq.le)

/-- The underlying function of `extByZeroCLM hS g` agrees `μ`-a.e. with
`S.indicator ⇑g`. -/
theorem extByZeroCLM_coeFn {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : Lp ℝ p (μ.restrict S)) :
    extByZeroCLM hS g =ᵐ[μ] S.indicator (g : α → ℝ) := by
  simp only [extByZeroCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact (memLp_indicator_of_restrict hS (Lp.memLp g)).coeFn_toLp

-- ============================================================================
-- § 2. The restriction map  Lp(μ) →L[ℝ] Lp(μ.restrict S)
-- ============================================================================

/-- **Restriction map.**  A class `f ∈ Lp ℝ p μ` restricts to a class in
`Lp ℝ p (μ.restrict S)`: the underlying function is unchanged, only the measure
shrinks to `μ.restrict S ≤ μ`.  This is a norm-nonincreasing continuous linear map,
the companion of `extByZeroCLM`. -/
noncomputable def restrictToLpCLM (S : Set α)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p μ →L[ℝ] Lp ℝ p (μ.restrict S) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict S).toLp _
      map_add' := fun f₁ f₂ => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((Lp.memLp (f₁ + f₂)).restrict S).coeFn_toLp,
          ((Lp.memLp f₁).restrict S).coeFn_toLp,
          ((Lp.memLp f₂).restrict S).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp f₁).restrict S).toLp _)
            (((Lp.memLp f₂).restrict S).toLp _),
          ae_restrict_of_ae (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        simp only [h12, hadd, h1, h2, hinner, Pi.add_apply]
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((Lp.memLp (c • f)).restrict S).coeFn_toLp,
          ((Lp.memLp f).restrict S).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp f).restrict S).toLp _),
          ae_restrict_of_ae (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        simp only [hcf, hsmul, hf, hinner, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] }
    1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have heq : ‖((Lp.memLp f).restrict S).toLp _‖
          = (eLpNorm (f : α → ℝ) p (μ.restrict S)).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.memLp f).restrict S).coeFn_toLp]
      rw [heq, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le _ _ _ _))

/-- The underlying function of `restrictToLpCLM S f` agrees `μ.restrict S`-a.e.
with the underlying function of `f`. -/
theorem restrictToLpCLM_coeFn (S : Set α) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p μ) :
    restrictToLpCLM S f =ᵐ[μ.restrict S] (f : α → ℝ) := by
  simp only [restrictToLpCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact ((Lp.memLp f).restrict S).coeFn_toLp

/-- `restrictToLpCLM` is norm-nonincreasing (pointwise form). -/
theorem restrictToLpCLM_norm_apply_le (S : Set α) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p μ) :
    ‖restrictToLpCLM S f‖ ≤ ‖f‖ := by
  have heq : ‖restrictToLpCLM S f‖ = (eLpNorm (f : α → ℝ) p (μ.restrict S)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (restrictToLpCLM_coeFn S f)]
  rw [heq, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le _ _ _ _)

/-- The operator norm of the restriction map is at most `1`. -/
theorem restrictToLpCLM_opNorm_le_one (S : Set α) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ‖(restrictToLpCLM S : Lp ℝ p μ →L[ℝ] Lp ℝ p (μ.restrict S))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by rw [one_mul]; exact restrictToLpCLM_norm_apply_le S f)

-- ============================================================================
-- § 3. The retraction:  restrictToLpCLM ∘ extByZeroCLM = id
-- ============================================================================

/-- **Retraction identity.**  Restricting the extension-by-zero of a class back to
`μ.restrict S` recovers the original class.  Thus `restrictToLpCLM S` is an explicit
left inverse of `extByZeroCLM`, exhibiting the latter as a split isometric embedding. -/
theorem restrictToLpCLM_extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : Lp ℝ p (μ.restrict S)) :
    restrictToLpCLM S (extByZeroCLM hS g) = g := by
  rw [Lp.ext_iff]
  filter_upwards [restrictToLpCLM_coeFn S (extByZeroCLM hS g),
    ae_restrict_of_ae (extByZeroCLM_coeFn hS g), ae_restrict_mem hS]
    with a har hae hmem
  rw [har, hae, Set.indicator_of_mem hmem]

/-- The composition `restrictToLpCLM S ∘L extByZeroCLM` is the identity CLM. -/
theorem restrictToLpCLM_comp_extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (restrictToLpCLM S).comp (extByZeroCLM (μ := μ) hS)
      = ContinuousLinearMap.id ℝ (Lp ℝ p (μ.restrict S)) := by
  refine ContinuousLinearMap.ext fun g => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact restrictToLpCLM_extByZeroCLM hS g

/-- `extByZeroCLM` is injective (immediate from the retraction identity). -/
theorem extByZeroCLM_injective {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Function.Injective (extByZeroCLM (μ := μ) (p := p) hS) := by
  intro g₁ g₂ h
  have h₁ := restrictToLpCLM_extByZeroCLM (μ := μ) hS g₁
  have h₂ := restrictToLpCLM_extByZeroCLM (μ := μ) hS g₂
  rw [← h₁, ← h₂, h]

end
