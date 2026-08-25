import Proofs.Erdos85MuNegThreeZeroFiveTerminal
import Proofs.Erdos85NegativeSignedJointFullClosure

/-! # Close the residual h305 callback in the negative signed-joint split -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem muNegThreeZeroFiveEndpointCallback_false
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16) :
    MuNegThreeZeroFiveEndpointCallback G c := by
  intro a b hab u v huinj hvinj hurange hvrange hu hv
  exact false_of_h305_source_or_transported
    G hfree hreg (by norm_num) c (by simpa using hc)
      a b hab u v huinj hvinj hurange hvrange hu hv

/-- With the honest h305 terminal installed, the general negative
signed-joint split has only its connected internal-factor frontier left. -/
theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected
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
    (hconnected : (G.induce c.supp).Connected → False) : False := by
  exact orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected_of_h305
    G hfree hreg c hc s mu hs_out hs_in hH hD x hx hconnected
      (muNegThreeZeroFiveEndpointCallback_false G hfree hreg c hc)

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveEndpointCallback_false
#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected
