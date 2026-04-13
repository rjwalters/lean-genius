/-
  Aristotle targets for Erdős Problem #353
  Routine supporting lemma for automated proof search.
  See Erdos353Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Standard measure theory fact (Lebesgue measure scaling under linear maps)
  - Clean theorem statement with no definition sorries
  - No axioms
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Basic

open MeasureTheory Set

namespace Erdos353Aristotle

/-- The preimage of a set of infinite Lebesgue measure under scaling by c ≠ 0
    also has infinite measure. This follows from the Haar measure scaling
    formula: volume(c⁻¹ • A) = |c|⁻ⁿ · volume(A) for n-dimensional Lebesgue measure. -/
theorem volume_preimage_smul_eq_top (c : ℝ) (hc : c ≠ 0)
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : MeasurableSet A) (hvol : volume A = ⊤) :
    volume ((fun x => c • x) ⁻¹' A) = ⊤ := by
  sorry

end Erdos353Aristotle
