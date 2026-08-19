import Proofs.Erdos85SixTenAllTriangleExteriorModel

/-!
# Exterior degrees of the high all-triangle `6+10` shape

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The graph-specific work is isolated to identifying the exterior-pair graph
with the explicit coordinate model.  The corrected model includes the
all-triangle ambient cycle edges at long offsets `±1`; it is six-regular, as
the general exterior Gram identity requires.
-/

open SimpleGraph

namespace Erdos85

/-- Any graph identified with the high `{\u00b13,\u00b14}` exterior-pair model is
six-regular.  This is a consistency check and a transport interface for the
global owner/hit-law obstruction. -/
theorem sixTenHigh_exteriorPair_equiv_sixRegular
    {X : Type*} [Fintype X] [DecidableEq X]
    (R : SimpleGraph X) [DecidableRel R.Adj]
    (e : SixTenVertex ≃ X)
    (hmodel : ∀ x y,
      R.Adj (e x) (e y) ↔ sixTenExteriorPairAdj sixTenHighDefectAdj x y) :
    ∀ y, R.degree y = 6 := by
  intro y
  let x : SixTenVertex := e.symm y
  have hey : e x = y := e.apply_symm_apply y
  have hcard : R.degree y =
      sixTenExteriorPairDegree sixTenHighDefectAdj x := by
    rw [← hey, SimpleGraph.degree]
    unfold sixTenExteriorPairDegree
    apply Finset.card_bij (fun y _ => e.symm y)
    · intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hyAdj : R.Adj (e x) y := by
        simpa [SimpleGraph.mem_neighborFinset] using hy
      simpa using (hmodel x (e.symm y)).mp (by simpa using hyAdj)
    · intro y₁ hy₁ y₂ hy₂ heq
      exact e.symm.injective heq
    · intro y hy
      refine ⟨e y, ?_, e.symm_apply_apply y⟩
      rw [SimpleGraph.mem_neighborFinset]
      have hyModel := (Finset.mem_filter.mp hy).2
      exact (hmodel x y).mpr hyModel
  rw [hcard]
  rcases x with i | i
  · exact sixTenHigh_short_exteriorPairDegree i
  · exact sixTenHigh_long_exteriorPairDegree i

end Erdos85

#print axioms Erdos85.sixTenHigh_exteriorPair_equiv_sixRegular
