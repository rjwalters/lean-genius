import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage
import Proofs.Erdos85BinarySquareMuThreeExteriorSignedPair

/-!
# Local-interface wrapper for the size-two `mu = 3` branch

This removes all derived global hypotheses from the exterior routing entry
point.  A caller supplies only the standard signed joint-line data on the
size-two component.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muThree_exterior_signedPair_dichotomy_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = 3 * s z)
    (u : V) (hu : u ∉ c.supp) :
    ∃ z z' : V,
      s z = 1 ∧ s z' = -1 ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧ z ≠ z' ∧
      ((G.Adj z z' → ∀ y, G.Adj u y → y ∉ c.supp →
          ¬ G.Adj z y ∧ ¬ G.Adj z' y) ∧
       (¬ G.Adj z z' →
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z y) ∧
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z' y))) := by
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s 3 hs_out hs_in hH hD
  exact orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair_dichotomy
    G hfree hreg hcard c hc s hs_in hs_out P.sum_eq_zero P.defectAction
      P.ambientAction_in P.ambientAction_out u hu

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muThree_exterior_signedPair_dichotomy_of_local
