import Proofs.Erdos85SizeTwoSignedJointNegativeReduction
import Proofs.Erdos85SizeTwoSwitchedJointExtension

/-!
# The unconditional ambient μ=3 terminal

Node: outline F.3 negative-lane assembly (the `hpos` obligation of the
orbit eliminator; squad msgs 13983/14177).

The switched-`μ=3` callback of the non-recursive orbit eliminator, as a
standalone theorem: an ambient signed joint at `θ = 3` on a size-two
component of the eight-regular binary square is impossible, with no
stratum or classification hypothesis — the checked `K`-symmetry native
classification covers every sector.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Unconditional switched-μ=3 kill.** -/
theorem false_of_orderSixtyFour_sizeTwo_ambient_muThree
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
    (s : V → ℤ) (hs : IsAmbientSignedJoint G c 3 s) : False := by
  obtain ⟨hs_out, hs_in, hH, hD⟩ := hs
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s 3 hs_out hs_in hH hD
  exact false_of_orderSixtyFour_mu3_jointEigenline_native_without_hA_out
    G hfree hreg hcard c hc s hs_in hs_out P.sum_eq_zero
      P.defectAction P.ambientAction_in

end

end Erdos85

#print axioms Erdos85.false_of_orderSixtyFour_sizeTwo_ambient_muThree
