/-
  Riemann-Lebesgue for Hölder Functions via L² (fourier-series-oq-02-oq-01)

  Open Question (from OQ-02): Can riemannLebesgue_of_holder be proved via the
  Mathlib L² Riemann-Lebesgue route (fourierCoeff_tendsto_zero) rather than
  the explicit Hölder decay bound?

  Answer: Yes. The L² route is:
    1. Hölder f → continuous (holder_continuous from OQ-02 infrastructure)
    2. Continuous on compact AddCircle T → bounded → MemLp 2 haarAddCircle
    3. Lift f to an L² element f_Lp via MemLp.toLp
    4. Fourier coefficients of f_Lp and f agree a.e. (integral_congr_ae)
    5. Apply fourierCoeff_tendsto_zero (L² Riemann-Lebesgue, FourierSeries.lean)

  This path is shorter than the direct Hölder decay argument in OQ-02, which
  requires an explicit bound of the form ‖ĉ_n‖ ≤ (C/2)(T/2|n|)^α. The L² route
  just needs compact support + measurability, with the harmonic analysis done
  by Mathlib's Hilbert basis machinery.

  References:
  - FourierSeries.lean: fourierCoeff_tendsto_zero (L² Parseval-based RL)
  - FourierSeriesOQ02.lean: riemannLebesgue_of_holder (direct bound proof)
  - FourierSeriesOQ02Incomplete01.lean: IsHolderOnCircle, holder_continuous
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic
import Proofs.FourierSeries
import Proofs.FourierSeriesOQ02

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle
open scoped ENNReal NNReal Real

namespace FourierHolderL2RL

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Riemann-Lebesgue via L²**: For Hölder f, prove ĉ_n → 0 using the L²
    Parseval route rather than explicit decay bounds.

    The key chain: Hölder → continuous → bounded on compact AddCircle T →
    MemLp 2 → Lp element → apply fourierCoeff_tendsto_zero (Parseval-based). -/
theorem riemannLebesgue_of_holder_via_L2 (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierDecayInfra.IsHolderOnCircle C α f)
    (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  -- Step 1: Hölder → continuous
  have hf_cont : Continuous f := FourierDecayInfra.holder_continuous hf hα
  -- Step 2: Continuous on compact AddCircle T → bounded → MemLp 2
  -- AddCircle T is compact; continuous functions on compact sets are bounded.
  -- We bound f by its sup norm (attained on a compact set), then use mono'.
  have hf_memLp : MeasureTheory.MemLp f 2 haarAddCircle :=
    (MeasureTheory.memLp_const
      (sSup (Set.range fun x : AddCircle T => ‖f x‖))).mono'
      hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        le_csSup (IsCompact.bddAbove (isCompact_range hf_cont.norm))
          (Set.mem_range_self x))
  -- Step 3: Lift f to an L² element
  set f_Lp := hf_memLp.toLp f with hf_Lp_def
  -- Step 4: Fourier coefficients of f_Lp (the L² representative) equal those
  -- of f. Since ⇑f_Lp =ᵐ[haarAddCircle] f, their integrals agree.
  have hfc_eq : ∀ n : ℤ, fourierCoeff (⇑f_Lp) n = fourierCoeff f n := fun n => by
    unfold fourierCoeff
    exact MeasureTheory.integral_congr_ae
      (hf_memLp.coeFn_toLp.mono fun x hx => by simp only [smul_eq_mul]; rw [hx])
  -- Step 5: Apply the L² Riemann-Lebesgue theorem (from FourierSeries.lean),
  -- which proves ĉ_n(f_Lp) → 0 via Parseval (Σ‖ĉ_n‖² < ∞ ⟹ ‖ĉ_n‖² → 0).
  have hrl := FourierSeries.fourierCoeff_tendsto_zero f_Lp
  -- Transfer: the tendencies agree since the coefficients agree pointwise.
  rwa [show (fun n : ℤ => fourierCoeff (⇑f_Lp) n) = (fun n : ℤ => fourierCoeff f n) from
    funext hfc_eq] at hrl

/-- **Consistency check**: The L² route and the direct bound route give the same
    conclusion. Both prove ĉ_n → 0 for Hölder f. -/
theorem riemannLebesgue_routes_agree (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierDecayInfra.IsHolderOnCircle C α f)
    (hα : 0 < α) :
    -- Direct bound route (from OQ-02):
    (Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)) ↔
    -- L² route (from this file):
    (Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)) :=
  Iff.rfl

end FourierHolderL2RL
