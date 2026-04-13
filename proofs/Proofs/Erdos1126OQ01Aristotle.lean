/-
  Aristotle targets for Erdős Problem #1126, OQ-01
  Measure-theoretic helper lemmas for the almost Jensen → almost additive proof.
  See Erdos1126OQ01Problem.lean for the main formalization.

  NOTE: The three null-set lemmas below have been proved manually in the main
  file using QuasiMeasurePreserving from Mathlib. This companion file is retained
  for reference but the sorries are now resolved in Erdos1126OQ01Problem.lean.

  The remaining sorry is ae_double_of_almost_jensen (Fubini section extraction),
  which requires the open conjecture-level argument and is NOT suitable for
  Aristotle automated proof search.
-/
import Mathlib
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory Set

namespace Erdos1126OQ01Aristotle

/- ## Null set preservation — PROVED in main file

These are now proved using:
- Measure.quasiMeasurePreserving_fst/snd (product measures)
- Measure.quasiMeasurePreserving_smul (Haar measure scaling)
-/

lemma volume_preimage_double_null {N : Set (ℝ × ℝ)} (hN : volume N = 0) :
    volume ((fun p : ℝ × ℝ => (2 * p.1, 2 * p.2)) ⁻¹' N) = 0 := by
  have heq : (fun p : ℝ × ℝ => (2 * p.1, 2 * p.2)) = ((2 : ℝ) • ·) := by
    ext ⟨a, b⟩ <;> simp [smul_eq_mul]
  rw [heq]
  exact (Measure.quasiMeasurePreserving_smul volume (two_ne_zero : (2 : ℝ) ≠ 0)).preimage_null hN

lemma volume_preimage_fst_null {S : Set ℝ} (hS : volume S = 0) :
    volume (Prod.fst ⁻¹' S : Set (ℝ × ℝ)) = 0 :=
  Measure.quasiMeasurePreserving_fst.preimage_null hS

lemma volume_preimage_snd_null {S : Set ℝ} (hS : volume S = 0) :
    volume (Prod.snd ⁻¹' S : Set (ℝ × ℝ)) = 0 :=
  Measure.quasiMeasurePreserving_snd.preimage_null hS

end Erdos1126OQ01Aristotle
