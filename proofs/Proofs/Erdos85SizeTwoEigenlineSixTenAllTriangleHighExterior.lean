import Proofs.Erdos85SixTenAllTriangleExteriorModel

/-!
# Exterior-degree exclusion of the high all-triangle `6+10` shape

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The graph-specific work is isolated to identifying the exterior-pair graph
with the explicit coordinate model.  Once that identification is available,
six-regularity contradicts the model's long-shore degree four.
-/

open SimpleGraph

namespace Erdos85

/-- An exterior-pair graph isomorphic to the high `{\u00b13,\u00b14}` `6+10`
model cannot be six-regular. -/
theorem false_of_sixTenHigh_exteriorPair_equiv
    {X : Type*} [Fintype X] [DecidableEq X]
    (R : SimpleGraph X) [DecidableRel R.Adj]
    (e : SixTenVertex ≃ X)
    (hmodel : ∀ x y,
      R.Adj (e x) (e y) ↔ sixTenExteriorPairAdj sixTenHighDefectAdj x y)
    (hreg : ∀ x, R.degree x = 6) : False := by
  let x : SixTenVertex := Sum.inr 0
  have hcard : R.degree (e x) =
      sixTenExteriorPairDegree sixTenHighDefectAdj x := by
    rw [SimpleGraph.degree]
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
  have hfour : sixTenExteriorPairDegree sixTenHighDefectAdj x = 4 := by
    exact sixTenHigh_long_exteriorPairDegree 0
  have hsix := hreg (e x)
  omega

end Erdos85

#print axioms Erdos85.false_of_sixTenHigh_exteriorPair_equiv
