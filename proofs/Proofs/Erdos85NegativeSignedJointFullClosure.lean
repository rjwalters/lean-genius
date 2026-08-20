import Proofs.Erdos85NegativeSignedJointDisconnectedClosure

/-! # Full negative signed-joint structural split

This is the exact parent socket of the disconnected normalization: every
regular order-64 negative signed joint is reduced either to the connected
internal `C16` frontier or to the single `h305` graph callback.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected_of_h305
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : Fin 64) (hx : x ∈ c.supp)
    (hconnected : (G.induce c.supp).Connected → False)
    (h305 : MuNegThreeZeroFiveEndpointCallback G c) :
    False := by
  classical
  let H := G.induce c.supp
  by_cases hconn : H.Connected
  · exact hconnected hconn
  · exact orderSixtyFour_regular_sizeTwo_signedJoint_false_of_not_connected_h305
      G hfree hreg c hc s mu hs_out hs_in hH hD x hx hconn h305

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected_of_h305
