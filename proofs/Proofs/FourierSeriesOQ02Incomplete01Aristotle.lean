/-
  Aristotle targets for FourierSeriesOQ02Incomplete01 (Fourier Decay Infrastructure)
  Routine functional analysis API steps for automated proof search.
  See FourierSeriesOQ02Incomplete01.lean for the main formalization.

  Five sorries bridge the proof that Hölder decay of Fourier coefficients
  implies Hölder continuity of the function:

  1. summable_norm_fourierCoeff_of_decay — ℤ p-series comparison
  2. fourier_lipschitz_bound — explicit Lipschitz constant of Fourier modes
  3. fourier_holder_bound — Hölder bound via rpow_interpolation
  4. holderWith_of_dist_bound — API bridge: dist-based → edist-based Hölder
  5. decay_implies_regularity' — main theorem (depends on 1-4)

  Targets 1 and 4 are most tractable for automated proof search.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace FourierDecayInfraAristotle

variable {T : ℝ} [hT : Fact (0 < T)]

/-
TARGET 1
Summability of Fourier coefficient norms when decay holds.

Statement: if ‖ĉ_n‖ ≤ C/|n|^β for n ≠ 0 and β > 1, then Summable (fun n : ℤ => ‖ĉ_n‖).

Strategy:
  a. n = 0: ‖ĉ_0‖ is a finite constant → summable by Summable.of_finset
  b. n ≠ 0: ‖ĉ_n‖ ≤ C_decay/|n|^β. Use Summable.of_norm_bounded with the ℤ p-series.
  c. ℤ p-series: Summable (fun n : ℤ => 1/|n|^β) follows from the ℕ p-series
     Real.summable_nat_rpow_inv (which requires β > 1) via Int.summable_iff.
-/
theorem summable_norm_fourierCoeff_of_decay (f : AddCircle T → ℂ) (C_decay : ℝ≥0) (β : ℝ)
    (hβ : 1 < β)
    (hdecay : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff f n‖ ≤ (C_decay : ℝ) / |↑n| ^ β) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖) := by
  sorry

/-
TARGET 2
Lipschitz bound for Fourier modes: ‖fourier n x - fourier n y‖ ≤ (2π|n|/T) · dist x y.

Strategy: fourier n x = exp(2πi·n·x/T). The exponential map is 1-Lipschitz on the unit
circle (|exp(ia) - exp(ib)| ≤ |a - b|). Composing with x ↦ (2πnx/T) gives the factor
2π|n|/T. Relevant Mathlib API: LipschitzWith or AddCircle.lipschitzWith_fourier.
-/
theorem fourier_lipschitz_bound (n : ℤ) (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤ 2 * Real.pi * |↑n| / T * dist x y := by
  sorry

/-
TARGET 3
Hölder bound for Fourier modes via interpolation.

Statement: ‖fourier n x - fourier n y‖ ≤ 2^{1-α} · (2π|n|/T)^α · dist(x,y)^α.

Strategy: Apply rpow_interpolation (proved in main file):
  a = ‖fourier n x - fourier n y‖ ≤ 2 (trivial bound, fourier_sub_norm_le_two)
  a ≤ (2π|n|/T) · dist x y   (Lipschitz bound, fourier_lipschitz_bound)
Then rpow_interpolation gives a ≤ 2^{1-α} · ((2π|n|/T) · dist x y)^α.
Finally split ((2π|n|/T) · dist x y)^α = (2π|n|/T)^α · dist(x,y)^α.
-/
theorem fourier_holder_bound (n : ℤ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤
      2 ^ (1 - α) * (2 * Real.pi * |↑n| / T) ^ α * dist x y ^ α := by
  sorry

/-
TARGET 4 (most tractable: pure API bridge)
Convert a dist-based Hölder bound to the edist-based HolderWith predicate.

HolderWith C α f means: ∀ x y, edist (f x) (f y) ≤ ↑C * edist x y ^ (α : ℝ)
We have:           h : ∀ x y, ‖f x - f y‖ ≤ ↑C * dist(x,y)^(α : ℝ)

Strategy:
  intro x y
  rw [edist_dist] at *   -- edist x y = ENNReal.ofReal (dist x y)
  For normed groups: edist (f x) (f y) = ‖f x - f y‖₊ (coerced)
  Then ENNReal.ofReal ‖f x - f y‖ ≤ ENNReal.ofReal (C * dist x y ^ α)
      = C * ENNReal.ofReal (dist x y ^ α) = C * edist x y ^ α.
-/
theorem holderWith_of_dist_bound {C : ℝ≥0} {α : ℝ≥0} {f : AddCircle T → ℂ}
    (h : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ (α : ℝ)) :
    HolderWith C α f := by
  sorry

/-
TARGET 5 (depends on 1-4)
Main theorem: Fourier coefficient decay implies Hölder continuity.

If f has Fourier coefficients decaying as O(1/|n|^β) with β > α+1,
then f is α-Hölder continuous.

Strategy: Uses summable_norm_fourierCoeff_of_decay (target 1),
Fourier inversion (hasSum_fourier_series_of_summable),
the term-by-term Hölder bound from fourier_holder_bound (target 3),
and holderWith_of_dist_bound (target 4) to assemble the conclusion.
-/
theorem decay_implies_regularity' (β α : ℝ) (hβα : α + 1 < β) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : C(AddCircle T, ℂ)) (C_decay : ℝ≥0)
    (hdecay : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff (⇑f) n‖ ≤ (C_decay : ℝ) / |↑n| ^ β) :
    ∃ (C_holder : ℝ≥0), HolderWith C_holder α.toNNReal ⇑f := by
  sorry

end FourierDecayInfraAristotle

end
