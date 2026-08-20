import Proofs.Erdos85C4FreeSubsetForbiddenCherryBound
import Proofs.Erdos85EdgeIndexedServiceNoCommonNeighbor
import Proofs.Erdos85EdgeIndexedServiceTypeHandshake

/-! # Shared-endpoint pairs forbidden from service two-walks -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Unordered pairs of shore-type-`2` exterior edges sharing a shore
endpoint. -/
def sharedEndpointShoreEdgePairFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    Finset (Finset R.edgeFinset) :=
  ((shoreTypeEdgeFinset R S 2).powersetCard 2).filter fun T ↦
    ∃ x ∈ S, ∀ a ∈ T, x ∈ a.1.toFinset

theorem sharedEndpointShoreEdgePairFinset_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    sharedEndpointShoreEdgePairFinset R S ⊆
      (shoreTypeEdgeFinset R S 2).powersetCard 2 := by
  intro T hT
  exact (Finset.mem_filter.mp hT).1

/-- The service matching law certifies that every shared-endpoint pair is a
forbidden target pair for the service-neighbor cherry count. -/
theorem sharedEndpointShoreEdgePairFinset_no_common_service_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (S : Finset V) (T : Finset R.edgeFinset)
    (hT : T ∈ sharedEndpointShoreEdgePairFinset R S)
    (d : R.edgeFinset) :
    ¬ T ⊆ Cedge.neighborFinset d := by
  classical
  have hcard : T.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨x, _, hx⟩ := (Finset.mem_filter.mp hT).2
  have hxa : x ∈ a.1.toFinset := hx a (by simp)
  have hxb : x ∈ b.1.toFinset := hx b (by simp)
  intro hsub
  have had : Cedge.Adj d a :=
    (Cedge.mem_neighborFinset d a).mp (hsub (by simp))
  have hbd : Cedge.Adj d b :=
    (Cedge.mem_neighborFinset d b).mp (hsub (by simp))
  exact edgeIndexedService_no_commonNeighbor_of_mem_mem
    H R Cedge hservice a b hab x hxa hxb
      ⟨d, (Cedge.adj_comm d a).mp had, (Cedge.adj_comm d b).mp hbd⟩

end

end Erdos85

#print axioms
  Erdos85.sharedEndpointShoreEdgePairFinset_no_common_service_neighbor
