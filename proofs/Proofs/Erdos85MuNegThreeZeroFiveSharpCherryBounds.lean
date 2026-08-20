import Proofs.Erdos85EdgeIndexedServiceSharedEndpointCherryBound
import Proofs.Erdos85MuNegThreeZeroFiveSharedEndpointPairCount
import Proofs.Erdos85MuNegThreeZeroFiveMiddleProfileParity

/-! # Sharp shared-endpoint cherry bounds in the corrected h305 geometry -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Removing the 24 pairs of same-shore exterior edges that share an endpoint
sharpens both shore-type cherry bounds from `66` to `42`. -/
theorem h305_correctShoreModes_sharp_cherry_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ a : R.edgeFinset,
      (serviceNeighborShoreTypeCount R Cedge a U 2).choose 2) ≤ 42 ∧
    (∑ a : R.edgeFinset,
      (serviceNeighborShoreTypeCount R Cedge a U 0).choose 2) ≤ 42 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let W := (Finset.univ : Finset (ZMod 8)).image v
  have hU12 : (shoreTypeEdgeFinset R U 2).card = 12 := by
    simpa [U] using h305_correctShoreMode_typeTwo_card_twelve
      R u huinj humode
  have hW12 : (shoreTypeEdgeFinset R W 2).card = 12 := by
    simpa [W] using h305_correctShoreMode_typeTwo_card_twelve
      R v hvinj hvmode
  have hU24 : (sharedEndpointShoreEdgePairFinset R U).card = 24 := by
    simpa [U] using h305_sharedEndpointShoreEdgePairFinset_card_twentyFour
      R u huinj humode
  have hW24 : (sharedEndpointShoreEdgePairFinset R W).card = 24 := by
    simpa [W] using h305_sharedEndpointShoreEdgePairFinset_card_twentyFour
      R v hvinj hvmode
  have htwo := edgeIndexedService_typeTwo_cherry_le_42_of_cards
    H R Cedge hservice hfree U hU12 hU24
  have hzero := edgeIndexedService_typeTwo_cherry_le_42_of_cards
    H R Cedge hservice hfree W hW12 hW24
  refine ⟨htwo, ?_⟩
  have hpart : Uᶜ = W := h305_shoreImages_compl_eq u v hdisj hcover
  simpa only [← hpart,
    serviceNeighborShoreTypeCount_zero_eq_two_compl R Cedge] using hzero

end

end Erdos85

#print axioms Erdos85.h305_correctShoreModes_sharp_cherry_bounds
