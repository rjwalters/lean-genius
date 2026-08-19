import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage
import Proofs.Erdos85MuThreeKSymmetryNativeClassification

/-!
# Reduction of signed size-two modes to the negative spectrum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The general signed-joint package has six possible integral defect
eigenvalues.  The positive modes `1` and `3` are already contradictory, so
this wrapper makes the true remaining frontier explicit: `-7,-5,-3,-1`.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Any local signed size-two joint eigenline is impossible once its four
negative eigenvalue cases are discharged.  The positive cases are closed
internally by the existing structural and checked-certificate terminals. -/
theorem orderSixtyFour_sizeTwo_signedJoint_false_of_negative_cases
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
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : V) (hx : x ∈ c.supp)
    (hnegSeven : mu = -7 → False)
    (hnegFive : mu = -5 → False)
    (hnegThree : mu = -3 → False)
    (hnegOne : mu = -1 → False) : False := by
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  rcases orderSixtyFour_sizeTwo_signedJoint_candidates_of_local
      G hfree hreg hcard c hc s mu hs_out hs_in hH hD x hx with
    hmu | hmu | hmu | hmu | hmu | hmu
  · exact hnegSeven hmu
  · exact hnegFive hmu
  · exact hnegThree hmu
  · exact hnegOne hmu
  · subst mu
    exact orderSixtyFour_sizeTwoPart_signedJointEigenvector_muOne_false
      G hfree hreg hcard c hc s hs_out
        (fun y hy => (hs_in y hy).symm) hH (by
          intro z hz
          simpa using hD z hz)
  · subst mu
    exact false_of_orderSixtyFour_mu3_jointEigenline_native_without_hA_out
      G hfree hreg hcard c hc s hs_in hs_out P.sum_eq_zero
        P.defectAction P.ambientAction_in

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_false_of_negative_cases
