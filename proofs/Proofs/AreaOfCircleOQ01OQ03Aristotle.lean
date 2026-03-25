/-
  Aristotle targets for Isoperimetric Inequality (area-of-circle-oq-01-oq-03)
  Routine supporting lemmas for automated proof search.
  See AreaOfCircleOQ01OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms

  These two lemmas are the remaining gaps in the proof that
  fourier_decomposition is a theorem (was axiom). Both have
  clear proof outlines using existing Mathlib lemmas.
-/
import Mathlib

open Real Filter Topology Complex MeasureTheory

noncomputable section

namespace IsoperimetricOQAristotle

/-
PROBLEM
The complex-valued function ofReal ∘ f is MemLp 2 on Ioc 0 (2π) when f is C¹.

PROVIDED SOLUTION
Since f is C¹, it is continuous. Then ofReal ∘ f is continuous (composition of continuous functions). A continuous function on any interval is in Lp for any p, because Ioc 0 (2π) has finite measure. Use Continuous.memLp_restrict or memLp_of_bounded_continuous or similar.
-/
lemma memLp_ofReal_comp_of_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    MemLp (ofReal ∘ f) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  refine' MeasureTheory.MemLp.mono' _ _ _;
  refine' fun x => ( SupSet.sSup ( Set.image ( fun y => |f y| ) ( Set.Icc 0 ( 2 * Real.pi ) ) ) );
  · exact MeasureTheory.memLp_const _;
  · exact Continuous.aestronglyMeasurable ( by exact Complex.continuous_ofReal.comp hf.continuous );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by simpa using le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image ( show Continuous fun y => |f y| from continuous_abs.comp hf.continuous ) ) ) ( Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hx ) ;

/-
PROBLEM
For a real number x, ‖ofReal x‖² = x².

PROVIDED SOLUTION
‖ofReal x‖ = |x| (by norm_ofReal or similar). Then |x|² = x² (by sq_abs). So ‖ofReal x‖² = x².
-/
lemma norm_ofReal_sq (x : ℝ) : ‖(ofReal x : ℂ)‖ ^ 2 = x ^ 2 := by
  norm_num [ ← sq_abs ]

/-
PROBLEM
Convert the interval integral of ‖ofReal ∘ f‖² to interval integral of f².

PROVIDED SOLUTION
The integrands are equal pointwise: ‖(ofReal ∘ f) t‖² = ‖ofReal (f t)‖² = (f t)² by norm_ofReal_sq. Use intervalIntegral.integral_congr or congrArg with ext.
-/
lemma intervalIntegral_norm_ofReal_sq (f : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..(2 * π), ‖(ofReal ∘ f) t‖ ^ 2 =
    ∫ t in (0 : ℝ)..(2 * π), (f t : ℝ) ^ 2 := by
  norm_num [ ← sq, norm_ofReal_sq ]

/-- Parseval identity for periodic real functions on [0, 2π]. -/
theorem parseval_periodic_real (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) (hab : (0 : ℝ) < 2 * π)
    (ĉ : ℤ → ℂ) (hĉ : ĉ = fun n => fourierCoeffOn hab (ofReal ∘ f) n) :
    (Summable fun n => ‖ĉ n‖ ^ 2) ∧
    ∫ t in (0 : ℝ)..(2 * π), (f t : ℝ) ^ 2 =
      (2 * π) * ∑' n : ℤ, ‖ĉ n‖ ^ 2 := by
  have hL2 := memLp_ofReal_comp_of_contDiff f hf
  have hparseval := hasSum_sq_fourierCoeffOn hab hL2
  -- hparseval : HasSum (fun i => ‖fourierCoeffOn hab (ofReal ∘ f) i‖ ^ 2)
  --   ((2π - 0)⁻¹ • ∫ x in 0..2π, ‖(ofReal ∘ f) x‖ ^ 2)
  subst hĉ
  constructor
  · exact hparseval.summable
  · have htsum := hparseval.tsum_eq
    rw [intervalIntegral_norm_ofReal_sq] at htsum
    simp only [sub_zero] at htsum
    -- htsum : ∑' i, ‖fourierCoeffOn hab (ofReal ∘ f) i‖ ^ 2 = (2π)⁻¹ • ∫ t in 0..2π, (f t)²
    -- Goal : ∫ t in 0..2π, (f t)² = 2π * ∑' i, ‖fourierCoeffOn hab (ofReal ∘ f) i‖ ^ 2
    rw [htsum, smul_eq_mul]
    field_simp

/-- IBP for Fourier coefficients of periodic functions on [0, 2π]. -/
theorem fourierCoeffOn_deriv_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv f) n =
    I * ↑n * fourierCoeffOn hab (ofReal ∘ f) n := by
  have := @fourierCoeffOn_of_hasDerivAt 0 (2 * Real.pi) hab (ofReal ∘ f) (ofReal ∘ deriv f) n
  norm_num at *
  have h_periodic : f (2 * Real.pi) = f 0 := by simpa using hperiod 0
  specialize this hn (fun x hx => ?_) (?_) <;> norm_num [h_periodic] at *
  · convert HasDerivAt.ofReal_comp
      (hasDerivAt_deriv_iff.mpr <| show DifferentiableAt ℝ f x from
        hf.contDiffAt.differentiableAt <| by norm_num) using 1
  · exact Continuous.intervalIntegrable
      (by exact Complex.continuous_ofReal.comp (hf.continuous_deriv le_rfl)) _ _
  · rw [this]; ring; norm_num [hn, Real.pi_ne_zero]; ring
    rw [show f (Real.pi * 2) = f 0 by simpa [mul_comm] using hperiod 0]; ring

end IsoperimetricOQAristotle