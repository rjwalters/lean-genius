import Proofs.Erdos85MuNegThreeOneTwoOrbitTerminal
import Proofs.Erdos85AmbientMuThreeUnconditional

/-!
# Unconditional positive-lane closure for the h312 orbit route

The checked h312 fixed-cell terminal and the global `mu=3` classifier leave
only the two negative ambient callbacks `mu=-5` and `mu=-1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The h312 eight-plus-eight lane is impossible once the ambient `-5` and
`-1` lanes are unavailable; the positive callback is discharged internally. -/
theorem false_of_orderSixtyFour_sizeTwo_muNegThree_eightEight_of_negativeTerminals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (h5 : ∀ w, IsAmbientSignedJoint G c (-5) w → False)
    (h1 : ∀ w, IsAmbientSignedJoint G c (-1) w → False) : False := by
  exact false_of_orderSixtyFour_sizeTwo_muNegThree_eightEight_of_crossLane_terminals
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv h5 h1
      (fun w hw ↦ false_of_orderSixtyFour_sizeTwo_ambient_muThree
        G hfree hreg hcard c hc w hw)

end

end Erdos85

#print axioms Erdos85.false_of_orderSixtyFour_sizeTwo_muNegThree_eightEight_of_negativeTerminals
