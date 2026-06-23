import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic
import Proofs.FourierSeries

/-
# Riemann-Lebesgue for Hölder Functions: Alternative L² Proof (OQ-02-OQ-01)

## Open Question

Can `riemannLebesgue_of_holder` be proved via the Parseval/L² route rather than
via the explicit quantitative bound ‖ĉ_n‖ ≤ (C/2)(T/2|n|)^α?

## Answer: Yes

The L² path:
  1. Hölder (α > 0) → Continuous  (`HolderWith.continuous`)
  2. Continuous on compact AddCircle T → bounded → MemLp 2 (compact + finite Haar)
  3. Lift f to Lp element f_Lp via `MemLp.toLp`
  4. Fourier coefficients agree: `fourierCoeff ⇑f_Lp n = fourierCoeff f n`
  5. Apply `FourierSeries.fourierCoeff_tendsto_zero` (Parseval: Σ‖ĉ_n‖² < ∞ → ĉ_n → 0)

This proof is ~15 lines vs ~90 lines for the quantitative bound approach.

## Significance

The L² path reveals that ĉ_n → 0 follows from L²-membership alone, not from
decay rates. The quantitative approach in OQ-02 gives more: it bounds ‖ĉ_n‖ ≤
(C/2)(T/2|n|)^α. But for the qualitative question (do coefficients tend to zero?)
the L² Parseval argument is shorter and conceptually cleaner.
-/

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle
open scoped ENNReal NNReal Real

namespace FourierHolderL2RL

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Riemann-Lebesgue via L²**: For Hölder f, prove ĉ_n → 0 using the Parseval route.

    Chain: Hölder → Continuous → MemLp 2 → Parseval (‖ĉ_n‖² summable) → ĉ_n → 0.
    Uses `HolderWith C α f` (Mathlib's Hölder predicate) directly.
    The conceptually natural path; quantitative decay (OQ-02) gives more but costs more. -/
theorem riemannLebesgue_of_holder_via_L2 (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : HolderWith C α f)
    (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  -- Step 1: Hölder → Continuous
  have hf_cont : Continuous f := hf.continuous hα
  -- Step 2: Continuous on compact AddCircle T → MemLp 2
  -- (bounded on compact → L^∞ → L² under finite Haar measure)
  have hf_memLp : MeasureTheory.MemLp f 2 haarAddCircle :=
    (MeasureTheory.memLp_const
      (sSup (Set.range fun x : AddCircle T => ‖f x‖))).mono'
      hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        le_csSup (IsCompact.bddAbove (isCompact_range hf_cont.norm))
          (Set.mem_range_self x))
  -- Step 3: Lift to L² representative
  set f_Lp := hf_memLp.toLp f
  -- Step 4: Fourier coefficients agree pointwise
  -- (⇑f_Lp =ᵐ[haarAddCircle] f, so ∫ fourier(-n)·⇑f_Lp = ∫ fourier(-n)·f)
  have hfc_eq : ∀ n : ℤ, fourierCoeff (⇑f_Lp) n = fourierCoeff f n := fun n => by
    unfold fourierCoeff
    exact MeasureTheory.integral_congr_ae
      (hf_memLp.coeFn_toLp.mono fun x hx => by simp only [smul_eq_mul]; rw [hx])
  -- Step 5: Parseval-based RL for f_Lp (from FourierSeries.lean), then transfer
  have hrl := FourierSeries.fourierCoeff_tendsto_zero f_Lp
  rwa [show (fun n : ℤ => fourierCoeff (⇑f_Lp) n) = (fun n : ℤ => fourierCoeff f n) from
    funext hfc_eq] at hrl

-- Verification
#check @riemannLebesgue_of_holder_via_L2

end FourierHolderL2RL
