import Proofs.Erdos85OrderSixtyFourMuThreeMixedGridAssembly

/-!
# Order-64 joint-eigenline `μ = 3` capstone

This is the final graph-facing socket for the signed size-two `μ = 3`
branch.  The structural argument constructs the actual mixed-grid code; a
shape/sector-specific `K`-classification and its checked certificates then
contradict that code.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A complete `K`-symmetry classification for the internal signed factor
rules out the corresponding order-64 joint eigenline. -/
theorem false_of_orderSixtyFour_mu3_jointEigenline
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (classification : MuThreeKSymmetryClassification
      (orderSixtyFourMuThreeInternalRel G
        (cSupp := c.supp) (s := s))) : False := by
  obtain ⟨label, hinj, code⟩ := orderSixtyFour_muThree_exists_mixedGridCode
    G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
  exact false_of_muThreeMixedGridCode_of_kSymmetryClassification
    (orderSixtyFourMuThreeInternalRel G)
    (orderSixtyFourMuThreeHole label)
    (orderSixtyFourMuThreeExteriorCellGraph G label hinj)
    classification code

end


end Erdos85

#print axioms Erdos85.false_of_orderSixtyFour_mu3_jointEigenline
