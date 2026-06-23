/-
# Glivenko-Cantelli: Proving the Indicator Integration Axioms
(laws-of-large-numbers-oq-04-oq-03)

The Glivenko-Cantelli formalization (`LawsOfLargeNumbersOQ04`) leaves two
integration facts as axioms:

  **Axiom 1** (`thresholdIndicator_integrable`):
    The threshold indicator 1_{Xᵢ(ω) ≤ x} is integrable on probability spaces.

  **Axiom 2** (`integral_thresholdIndicator_eq_cdf`):
    E[1_{X₀(ω) ≤ x}] = F(x), i.e., the integral of the indicator equals the CDF.

Both are provable from Mathlib's integration API. We prove them here, eliminating
two of the three axioms in the Glivenko-Cantelli formalization. The third
assumption (the finite bracketing uniformity step) was originally declared as
axiom `glivenko_cantelli_uniform` in the parent; S6 proved it in the bracketing
companion (`LawsOfLargeNumbersOQ04OQ03Bracketing.lean`) from the smaller
real-analytic axiom `bracketingGrid_exists`, and S7 retired the parent's axiom.

## Key Mathlib Lemmas Used

- `Integrable.mono'`: bounded + measurable + finite measure → integrable
- `MeasureTheory.integral_indicator`: ∫ s.indicator f = ∫ in s, f
- `MeasureTheory.integral_const`: ∫ _, c ∂μ = (μ univ).toReal • c
- `Measure.restrict_apply`: (μ.restrict s) t = μ (t ∩ s) for measurable t

## Result

Axiom count reduced: 3 → 1 (only the real-analytic `bracketingGrid_exists`
remains axiomatic; lives in the bracketing companion).

## Axiom Count: 0
## Sorry Count: 0
-/

import Proofs.LawsOfLargeNumbersOQ04
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- ============================================================================
-- Proof of Axiom 1: Threshold Indicators Are Integrable
-- ============================================================================

/-- **Proved (was Axiom 1)**: Threshold indicators 1_{X₀(ω) ≤ x} are integrable
    on probability spaces.

    The indicator takes values 0 or 1, so |thresholdIndicator| ≤ 1.
    Since the constant function 1 is integrable on any probability space,
    `Integrable.mono'` gives integrability of the bounded measurable indicator. -/
theorem thresholdIndicator_integrable_proved
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (x : ℝ) :
    Integrable (thresholdIndicator X x 0) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact ((measurable_iic_indicator x).comp (hX 0)).aestronglyMeasurable
  · filter_upwards with ω
    simp only [thresholdIndicator, Set.indicator]
    split_ifs with h
    · norm_num
    · norm_num

-- ============================================================================
-- Proof of Axiom 2: Integral of Indicator Equals CDF
-- ============================================================================

/-- The threshold indicator factors through the preimage indicator. -/
private lemma thresholdIndicator_eq_preimage_indicator_fun
    {X : ℕ → Ω → ℝ} (x : ℝ) :
    (fun ω => thresholdIndicator X x 0 ω) =
    (fun ω => (X 0 ⁻¹' Set.Iic x).indicator (fun _ => (1 : ℝ)) ω) := by
  ext ω
  simp only [thresholdIndicator, Set.indicator, Set.mem_preimage, Set.mem_Iic]

/-- **Proved (was Axiom 2)**: The expected value of the threshold indicator equals
    the true CDF.

    **Proof chain**:
    1. Rewrite the integrand: 1_{X₀ ≤ x}(ω) = (X 0 ⁻¹' Iic x).indicator(ω)
    2. Apply `integral_indicator` to convert to set integral on the preimage set
    3. Apply `integral_const` to evaluate ∫ in s, 1 ∂μ = (μ s).toReal
    4. Use `Measure.restrict_apply` + `Set.univ_inter` to get μ (X 0 ⁻¹' Iic x)
    5. Identify X 0 ⁻¹' Iic x = {ω | X 0 ω ≤ x} = trueCDF domain -/
theorem integral_thresholdIndicator_eq_cdf_proved
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (x : ℝ) :
    μ[thresholdIndicator X x 0] = trueCDF X μ x := by
  -- Preimage set is measurable
  have hms : MeasurableSet (X 0 ⁻¹' Set.Iic x) := (hX 0) measurableSet_Iic
  -- Step 1: Rewrite integrand via preimage indicator
  simp_rw [thresholdIndicator_eq_preimage_indicator_fun]
  -- Step 2: Convert to set integral on preimage
  rw [integral_indicator hms]
  -- Step 3: Evaluate constant integral: ∫ in s, 1 ∂μ = (μ s).toReal
  -- Post Mathlib bump: integral_const produces `(μ.restrict s).real univ • c`
  -- via the new `Measure.real` field, so unfold via measureReal_def + restrict_apply_univ.
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply_univ]
  -- Step 4: Identify with trueCDF (preimage of Iic is defeq to set-builder form)
  rfl

-- ============================================================================
-- Application: Pointwise Convergence Without Integration Axioms
-- ============================================================================

/-- **Corollary**: Pointwise convergence of empirical CDF using only proved lemmas
    (no integration axioms; the chain's sole remaining axiom is the real-analytic
    `bracketingGrid_exists` in the bracketing companion). -/
theorem empiricalCDF_pointwise_convergence_no_axiom
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (x : ℝ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => empiricalCDF X n x ω)
        Filter.atTop (nhds (trueCDF X μ x)) := by
  -- Proved integrability (replaces axiom 1)
  have hint : Integrable (thresholdIndicator X x 0) μ :=
    thresholdIndicator_integrable_proved hX_meas x
  -- Independence of indicators
  have hindep := thresholdIndicator_pairwise_indep hX_iid x
  -- Identical distribution of indicators
  have hident := thresholdIndicator_identDistrib x hX_ident
  -- Apply SLLN
  have hslln := strong_law_ae_real (thresholdIndicator X x) hint hindep hident
  -- Proved integral identity (replaces axiom 2)
  rw [integral_thresholdIndicator_eq_cdf_proved hX_meas x] at hslln
  -- Extract pointwise convergence
  filter_upwards [hslln] with ω hω
  convert hω using 1
  ext n
  simp only [empiricalCDF_eq_mean]

-- ============================================================================
-- Axiom Status Summary
-- ============================================================================

/-
Summary: the Glivenko-Cantelli axiom count has been reduced from 3 to 1, and
the **shape** of that one remaining axiom has shifted twice since this file
was written.

  - ✓ `thresholdIndicator_integrable` → proved as `thresholdIndicator_integrable_proved`
  - ✓ `integral_thresholdIndicator_eq_cdf` → proved as `integral_thresholdIndicator_eq_cdf_proved`
  - ✓ `glivenko_cantelli_uniform` → proved in `LawsOfLargeNumbersOQ04OQ03Bracketing`
        from the smaller real-analytic axiom `bracketingGrid_exists` (S4–S6),
        and the parent's axiom was retired in S7.
  - ✗ `bracketingGrid_exists` (S3 axiom) **was refuted** in S10 ACT (PR #20969):
        the structure is provably empty for any CDF with an atom of mass `> ε`,
        so adding the axiom made the namespace inconsistent. The disproof lives
        in `LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean`
        (`bracketingGrid_exists_false : False`, build-verified, 3122 jobs).
  - 🛠 `QuantileBracketingGrid` (S13 scaffold, this file's companion
        `LawsOfLargeNumbersOQ04OQ03QuantileBracketing.lean`) is the
        redesigned structure that **does** handle atomic CDFs: it replaces
        the refuted `step_le : F (qⱼ₊₁) - F (qⱼ) ≤ ε` with the quantile
        bound `Function.leftLim F (qⱼ₊₁) - F (qⱼ) ≤ ε` and drops the
        `cont` field. For atomless `F` left limits equal values, so the
        redesign is conservative.

The chain's sole remaining axiom is still `bracketingGrid_exists` in the
bracketing companion (kept in tree until the S14+ redesign supersedes it).
Its **content** is now known to be false; the real upstream target is the
quantile / `Function.leftLim`-based grid-existence lemma — *not* the
originally proposed `Monotone.exists_increasing_continuity_seq` (which is
about continuous monotone functions and cannot recover the atomic-CDF case).

The pointwise convergence theorem (`empiricalCDF_pointwise_convergence_no_axiom`)
is independent of this design pivot and remains fully proved from Mathlib
without any integration axioms.
-/

end GlivenkoCantelli
