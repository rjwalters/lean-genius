/-
  Aristotle targets for Erdős Problem #1126, OQ-01
  Measure-theoretic helper lemmas for the almost Jensen → almost additive proof.
  See Erdos1126OQ01Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known results from measure theory (Fubini, null set preservation)
  - Clean theorem statements with no definition sorries
  - No axiom declarations

  These lemmas support the proof of almost_jensen_implies_almost_additive_shifted.
  The main theorem's algebraic structure is proved; these are the remaining
  measure-theoretic gaps.
-/
import Mathlib
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set

namespace Erdos1126OQ01Aristotle

/-! ## Null set preservation under linear maps and projections -/

/-- Preimage of a null set under the scaling map (x,y) ↦ (2x,2y) is null.
The map has determinant 4, so volume scales by 1/4. -/
lemma volume_preimage_double_null {N : Set (ℝ × ℝ)} (hN : volume N = 0) :
    volume ((fun p : ℝ × ℝ => (2 * p.1, 2 * p.2)) ⁻¹' N) = 0 := by
  sorry

/-- Preimage of a 1D null set under first projection is null in ℝ².
Follows from volume(S × ℝ) = volume(S) · volume(ℝ) = 0 · ∞ = 0 in ENNReal. -/
lemma volume_preimage_fst_null {S : Set ℝ} (hS : volume S = 0) :
    volume (Prod.fst ⁻¹' S : Set (ℝ × ℝ)) = 0 := by
  sorry

/-- Preimage of a 1D null set under second projection is null in ℝ². -/
lemma volume_preimage_snd_null {S : Set ℝ} (hS : volume S = 0) :
    volume (Prod.snd ⁻¹' S : Set (ℝ × ℝ)) = 0 := by
  sorry

end Erdos1126OQ01Aristotle
