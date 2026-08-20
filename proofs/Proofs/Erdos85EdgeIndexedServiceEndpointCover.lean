import Proofs.Erdos85EdgeIndexedServiceUniqueMatching

/-! # Endpoint cover of an edge-indexed service neighborhood -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The support vertices covered by the endpoint pairs of the service
neighbors of an exterior edge. -/
def serviceNeighborEndpointCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) : Finset V :=
  (Cedge.neighborFinset a).biUnion fun b ↦ b.1.toFinset

/-- The six neighboring endpoint pairs cover exactly the vertices adjacent in
`H` to neither endpoint of the central exterior edge. -/
theorem edgeIndexedService_neighborEndpointCover_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a : R.edgeFinset) :
    serviceNeighborEndpointCover R Cedge a =
      Finset.univ.filter fun u ↦
        (internalEndpointNeighborFinset H R u a).card = 0 := by
  classical
  ext u
  simp only [serviceNeighborEndpointCover, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  exact edgeIndexedService_exists_incidentNeighbor_iff
    H R Cedge hservice u a

/-- Membership in the endpoint cover has a unique witnessing service edge. -/
theorem edgeIndexedService_endpointCover_existsUnique
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a : R.edgeFinset) (u : V)
    (hu : u ∈ serviceNeighborEndpointCover R Cedge a) :
    ∃! b : R.edgeFinset, Cedge.Adj a b ∧ u ∈ b.1.toFinset := by
  rw [edgeIndexedService_neighborEndpointCover_eq H R Cedge hservice a] at hu
  exact edgeIndexedService_unique_incidentNeighbor H R Cedge hservice u a
    (Finset.mem_filter.mp hu).2

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_neighborEndpointCover_eq
