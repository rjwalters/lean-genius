/-
  Lp Riesz representation for σ-finite measures: main theorem `riesz_lp_surjective_sigma_finite`, assembled from the split Infra/Norm/Loc pieces.

  Split out of the monolithic `CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean` (S20, researcher-15).
  Rationale: with the S18 drift fixes applied, the combined 1020-line file
  elaborates past the 32GB/40min Docker build envelope, so its error summary
  never flushes. Splitting each ≥300-line theorem into its own file makes each
  piece elaborate independently and within budget, and makes any residual
  Mathlib-drift errors measurable per-file. Same namespace / same public names,
  so downstream imports are unaffected.
-/
import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01Loc

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

-- ============================================================================
-- § 6. Main theorem
-- ============================================================================

theorem riesz_lp_surjective_sigma_finite
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  obtain ⟨g, hg_lq, hg_norm, hagree⟩ := localization_existence p q hp1 hptop hpq φ
  refine ⟨g, hg_lq, hg_norm, ?_⟩
  apply integral_representation_sf p q hp1 hptop hpq φ g hg_lq
  intro E hE hfin
  have heq : (indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop).toLp _ =
      (memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ := rfl
  rw [heq]
  exact hagree E hE hfin

end RieszSigmaFiniteComplete

end
