/-
# Glivenko-Cantelli Theorem (laws-of-large-numbers-oq-04)

The Glivenko-Cantelli theorem is the "uniform law of large numbers": for i.i.d. real-valued
random variables X₁, X₂, ... with CDF F(x) = P(X₁ ≤ x), the empirical CDF converges
uniformly to F almost surely:

  sup_{x∈ℝ} |Fₙ(x) - F(x)| → 0   a.s.

where Fₙ(x) = (1/n) |{i ≤ n : Xᵢ ≤ x}|.

## Proof Strategy

**Step 1 (PROVED)**: For each fixed x, the indicators 1_{Xᵢ ≤ x} are i.i.d. Bernoulli(F(x))
  random variables (by `IdentDistrib.comp` and `iIndepFun.comp`). SLLN gives
  Fₙ(x) → F(x) a.s. for each x.

**Step 2 (PROVED in companion `LawsOfLargeNumbersOQ04OQ03Bracketing.lean`)**:
  For any ε > 0, choose finitely many continuity points q₁,...,qₖ of F
  partitioning ℝ with F-mass < ε per interval. On the finite grid, pointwise convergence
  holds simultaneously a.s. (finite intersection). For any x between grid points,
  |Fₙ(x) - F(x)| ≤ max_j |Fₙ(qⱼ) - F(qⱼ)| + ε, giving uniform convergence.

## Axioms

The two integration facts that were previously axiomatic
(`thresholdIndicator_integrable` and `integral_thresholdIndicator_eq_cdf`) are now
proved in this file using Mathlib's bounded-measurable integrability (`Integrable.mono'`)
and the integral-indicator API.

The bracketing uniformity step (`glivenko_cantelli_uniform`), previously declared
as an axiom in this file, has been **retired** in S7: the bracketing companion
`LawsOfLargeNumbersOQ04OQ03Bracketing.lean` proves it from the smaller, purely
real-analytic axiom `bracketingGrid_exists` (the only Mathlib gap remaining in
the entire Glivenko-Cantelli chain).

This file is therefore fully axiom-free; the chain's sole remaining assumption
sits in the bracketing companion, with content
`Monotone.exists_increasing_continuity_seq` — the natural Mathlib upstream target.
-/

import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Definitions -/

/-- The empirical CDF at threshold x using the first n samples -/
noncomputable def empiricalCDF (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω)

/-- The true CDF: probability that X₀ ≤ x -/
noncomputable def trueCDF (X : ℕ → Ω → ℝ) (μ : Measure Ω) (x : ℝ) : ℝ :=
  (μ {ω | X 0 ω ≤ x}).toReal

/-- The threshold indicator: 1 if Xᵢ(ω) ≤ x, else 0 -/
noncomputable def thresholdIndicator (X : ℕ → Ω → ℝ) (x : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω)

/-! ## Basic Identities -/

/-- Empirical CDF is the sample mean of threshold indicators -/
theorem empiricalCDF_eq_mean (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (ω : Ω) :
    empiricalCDF X n x ω = (∑ i ∈ Finset.range n, thresholdIndicator X x i ω) / n := by
  simp only [empiricalCDF, thresholdIndicator]; ring

/-- Threshold indicator is composition with indicator function -/
theorem thresholdIndicator_eq_comp (X : ℕ → Ω → ℝ) (x : ℝ) (i : ℕ) :
    thresholdIndicator X x i = Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) ∘ X i := by
  ext ω; simp [thresholdIndicator]

/-! ## Measurability -/

/-- v ↦ 1_{v ≤ x} is Borel measurable as a function ℝ → ℝ -/
theorem measurable_iic_indicator (x : ℝ) :
    Measurable (Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) : ℝ → ℝ) :=
  measurable_const.indicator measurableSet_Iic

/-! ## Identical Distribution of Indicators -/

/-- If X i and X 0 are identically distributed, so are threshold indicators -/
theorem thresholdIndicator_identDistrib {X : ℕ → Ω → ℝ} (x : ℝ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (i : ℕ) :
    IdentDistrib (thresholdIndicator X x i) (thresholdIndicator X x 0) μ μ := by
  simp only [thresholdIndicator_eq_comp]
  exact (hident i).comp (measurable_iic_indicator x)

/-! ## Independence of Indicators -/

/-- If the X i are i.i.d. (as iIndepFun), the threshold indicators are pairwise independent -/
theorem thresholdIndicator_pairwise_indep {X : ℕ → Ω → ℝ}
    (hX_iid : iIndepFun X μ) (x : ℝ) :
    Pairwise (fun i j => thresholdIndicator X x i ⟂ᵢ[μ] thresholdIndicator X x j) := by
  have h_comp : iIndepFun (fun i ω => thresholdIndicator X x i ω) μ :=
    hX_iid.comp (fun _ => Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)))
                (fun _ => measurable_iic_indicator x)
  intro i j hij
  exact h_comp.indepFun hij

/-! ## Integration Facts (formerly axioms, now proved) -/

/-- **PROVED** (formerly axiom): Threshold indicators are integrable on probability
    spaces. They are bounded measurable functions on a finite-measure space, so
    `Integrable.mono'` against the constant function `1` gives integrability. -/
theorem thresholdIndicator_integrable [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (x : ℝ) :
    Integrable (thresholdIndicator X x 0) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact ((measurable_iic_indicator x).comp (hX 0)).aestronglyMeasurable
  · filter_upwards with ω
    simp only [thresholdIndicator, Set.indicator]
    split_ifs with h
    · norm_num
    · norm_num

/-- The threshold indicator factors through the preimage indicator. -/
private lemma thresholdIndicator_eq_preimage_indicator_fun
    {X : ℕ → Ω → ℝ} (x : ℝ) :
    (fun ω => thresholdIndicator X x 0 ω) =
    (fun ω => (X 0 ⁻¹' Set.Iic x).indicator (fun _ => (1 : ℝ)) ω) := by
  ext ω
  simp only [thresholdIndicator, Set.indicator, Set.mem_preimage, Set.mem_Iic]

/-- **PROVED** (formerly axiom): The expected value of the threshold indicator equals
    the true CDF. The proof rewrites the indicator via its preimage form, applies
    `integral_indicator` to convert to a set integral, then evaluates the constant
    integral as the measure of the preimage set. -/
theorem integral_thresholdIndicator_eq_cdf [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (x : ℝ) :
    μ[thresholdIndicator X x 0] = trueCDF X μ x := by
  have hms : MeasurableSet (X 0 ⁻¹' Set.Iic x) := (hX 0) measurableSet_Iic
  simp_rw [thresholdIndicator_eq_preimage_indicator_fun]
  rw [integral_indicator hms, integral_const, smul_eq_mul, mul_one,
      measureReal_def, Measure.restrict_apply_univ]
  rfl

/-! ## Pointwise Convergence (proved) -/

/-- **PROVED**: For each fixed threshold x, the empirical CDF converges a.s. to the true CDF.
    Uses the strong law of large numbers applied to i.i.d. indicator functions 1_{Xᵢ ≤ x}. -/
theorem empiricalCDF_pointwise_convergence [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (x : ℝ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => empiricalCDF X n x ω)
        Filter.atTop (nhds (trueCDF X μ x)) := by
  -- Apply SLLN to threshold indicators Y i = 1_{X i ≤ x}
  have hint := thresholdIndicator_integrable (μ := μ) hX_meas x
  have hindep := thresholdIndicator_pairwise_indep hX_iid x
  have hident := thresholdIndicator_identDistrib x hX_ident
  have hslln := strong_law_ae_real (thresholdIndicator X x) hint hindep hident
  -- Identify E[Y_0] = trueCDF X μ x
  rw [integral_thresholdIndicator_eq_cdf hX_meas x] at hslln
  -- Rewrite empiricalCDF as the ratio form from SLLN
  filter_upwards [hslln] with ω hω
  convert hω using 1
  ext n
  simp only [empiricalCDF_eq_mean]

/-! ## Uniform Convergence (Glivenko-Cantelli)

    The **uniform convergence theorem** `glivenko_cantelli_uniform` was previously
    declared as an axiom in this file. It has been retired in S7: the bracketing
    companion `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` proves it (via finite
    bracketing of continuity points) from the strictly weaker, purely real-analytic
    axiom `bracketingGrid_exists`. See that companion for the proved theorem.
-/

/-! ## Structural Properties -/

/-- Empirical CDF is non-decreasing in x (monotone in threshold) -/
theorem empiricalCDF_mono (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {x y : ℝ} (hxy : x ≤ y) :
    empiricalCDF X n x ω ≤ empiricalCDF X n y ω := by
  simp only [empiricalCDF]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  exact Set.indicator_le_indicator_of_subset (Set.Iic_subset_Iic.mpr hxy)
          (fun _ => zero_le_one) _

/-- True CDF is non-decreasing -/
theorem trueCDF_mono [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    trueCDF X μ x ≤ trueCDF X μ y := by
  simp only [trueCDF]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  exact measure_mono (fun ω hω => le_trans hω hxy)

/-- Empirical CDF is non-negative -/
theorem empiricalCDF_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (ω : Ω) :
    0 ≤ empiricalCDF X n x ω := by
  simp only [empiricalCDF]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  simp only [Set.indicator]
  split_ifs <;> norm_num

/-- True CDF is non-negative -/
theorem trueCDF_nonneg (X : ℕ → Ω → ℝ) (x : ℝ) :
    0 ≤ trueCDF X μ x :=
  ENNReal.toReal_nonneg

/-- The relationship: pointwise convergence implies error at each x vanishes a.s. -/
theorem empiricalCDF_error_vanishes [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (x : ℝ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n => empiricalCDF X n x ω - trueCDF X μ x)
        Filter.atTop (nhds 0) := by
  filter_upwards [empiricalCDF_pointwise_convergence hX_meas hX_iid hX_ident x] with ω hω
  have := hω.sub_const (trueCDF X μ x)
  simp only [sub_self] at this
  exact this

end GlivenkoCantelli
