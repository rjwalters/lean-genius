import Proofs.Erdos85EdgeIndexedServiceEndpointCover

/-! # Shore mass in an edge-indexed service neighborhood -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Because the neighboring service edges form a matching, counting their
endpoints inside any vertex set is the same as intersecting that set with the
whole endpoint cover. -/
theorem edgeIndexedService_sum_neighbor_endpoint_inter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a : R.edgeFinset) (S : Finset V) :
    ∑ b ∈ Cedge.neighborFinset a, (b.1.toFinset ∩ S).card =
      (serviceNeighborEndpointCover R Cedge a ∩ S).card := by
  classical
  let T : R.edgeFinset → Finset V := fun b ↦ b.1.toFinset ∩ S
  have hp : (Cedge.neighborFinset a : Set R.edgeFinset).PairwiseDisjoint T := by
    intro b hb d hd hbd
    have hab : Cedge.Adj a b := (Cedge.mem_neighborFinset a b).mp hb
    have had : Cedge.Adj a d := (Cedge.mem_neighborFinset a d).mp hd
    exact (edgeIndexedService_neighborEdges_pairwiseDisjoint
      H R Cedge hservice a b d hab had hbd).mono
        Finset.inter_subset_left Finset.inter_subset_left
  have hunion : (Cedge.neighborFinset a).biUnion T =
      serviceNeighborEndpointCover R Cedge a ∩ S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨b, hb, hxb⟩
      have hx' := Finset.mem_inter.mp hxb
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨b, hb, hx'.1⟩,
        hx'.2⟩
    · intro hx
      have hx' := Finset.mem_inter.mp hx
      rcases Finset.mem_biUnion.mp hx'.1 with ⟨b, hb, hxb⟩
      exact Finset.mem_biUnion.mpr ⟨b, hb,
        Finset.mem_inter.mpr ⟨hxb, hx'.2⟩⟩
  change ∑ b ∈ Cedge.neighborFinset a, (T b).card = _
  rw [← hunion, Finset.card_biUnion hp]

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_sum_neighbor_endpoint_inter_card
