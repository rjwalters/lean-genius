import Proofs.Erdos85EdgeIndexedServiceSharedEndpointForbiddenPairs

/-! # Sharpened service cherry bound from shared endpoints -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- C4-freeness gives the ordinary cherry bound on a shore-type edge set;
the service matching law removes every pair sharing an exterior endpoint. -/
theorem edgeIndexedService_typeTwo_cherry_le_choose_sub_sharedEndpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge) (S : Finset V) :
    (∑ a : R.edgeFinset,
      (serviceNeighborShoreTypeCount R Cedge a S 2).choose 2) ≤
      (shoreTypeEdgeFinset R S 2).card.choose 2 -
        (sharedEndpointShoreEdgePairFinset R S).card := by
  classical
  let E := shoreTypeEdgeFinset R S 2
  let F := sharedEndpointShoreEdgePairFinset R S
  have hbound :=
    sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
      Cedge hfree E F
      (by simpa [E, F] using sharedEndpointShoreEdgePairFinset_subset R S)
      (by
        intro T hT d
        exact sharedEndpointShoreEdgePairFinset_no_common_service_neighbor
          H R Cedge hservice S T (by simpa [F] using hT) d)
  change (∑ a : R.edgeFinset,
    (serviceNeighborShoreTypeCount R Cedge a S 2).choose 2) ≤
      E.card.choose 2 - F.card
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold serviceNeighborShoreTypeCount
  congr 1
  ext b
  simp [E, shoreTypeEdgeFinset, and_comm]

end

end Erdos85

#print axioms
  Erdos85.edgeIndexedService_typeTwo_cherry_le_choose_sub_sharedEndpoint
