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
import Mathlib

open MeasureTheory Set Pointwise
open scoped ENNReal

namespace Erdos353Aristotle

/-- The preimage of a set of infinite Lebesgue measure under scaling by c ≠ 0
    also has infinite measure. This follows from the Haar measure scaling
    formula: volume(c⁻¹ • A) = |c|⁻ⁿ · volume(A) for n-dimensional Lebesgue measure. -/
theorem volume_preimage_smul_eq_top (c : ℝ) (hc : c ≠ 0)
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : MeasurableSet A) (hvol : volume A = ⊤) :
    volume ((fun x => c • x) ⁻¹' A) = ⊤ := by
  -- Rewrite preimage as c⁻¹ • A
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 2) => c • x) ⁻¹' A = c⁻¹ • A := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_preimage]
    constructor
    · intro h; exact ⟨c • x, h, inv_smul_smul₀ hc x⟩
    · rintro ⟨a, ha, rfl⟩; rwa [smul_inv_smul₀ hc]
  rw [h_eq, MeasureTheory.Measure.addHaar_smul volume c⁻¹ A, hvol]
  exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
    (abs_pos.mpr (pow_ne_zero _ (inv_ne_zero hc))))

end Erdos353Aristotle
