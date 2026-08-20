import Proofs.Erdos85EdgeIndexedServiceTwoWalkLaw

/-! # No common service neighbor for intersecting exterior edges -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Distinct exterior edges sharing an endpoint have no common neighbor in
the service graph.  A common service neighbor would see two endpoint pairs
that the matching law requires to be disjoint. -/
theorem edgeIndexedService_no_commonNeighbor_of_mem_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a b : R.edgeFinset) (hab : a ≠ b) (u : V)
    (hua : u ∈ a.1.toFinset) (hub : u ∈ b.1.toFinset) :
    ¬ ∃ d : R.edgeFinset, Cedge.Adj a d ∧ Cedge.Adj b d := by
  rintro ⟨d, had, hbd⟩
  have hdisj := edgeIndexedService_neighborEdges_pairwiseDisjoint
    H R Cedge hservice d a b ((Cedge.adj_comm a d).mp had)
      ((Cedge.adj_comm b d).mp hbd) hab
  rw [Finset.disjoint_left] at hdisj
  exact hdisj hua hub

/-- Neighbor-finset form of the same zero common-neighbor law. -/
theorem edgeIndexedService_neighborFinset_inter_eq_empty_of_mem_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a b : R.edgeFinset) (hab : a ≠ b) (u : V)
    (hua : u ∈ a.1.toFinset) (hub : u ∈ b.1.toFinset) :
    Cedge.neighborFinset a ∩ Cedge.neighborFinset b = ∅ := by
  classical
  ext d
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro had hbd
  have had' := (Cedge.mem_neighborFinset a d).mp had
  have hbd' := (Cedge.mem_neighborFinset b d).mp hbd
  exact edgeIndexedService_no_commonNeighbor_of_mem_mem
    H R Cedge hservice a b hab u hua hub ⟨d, had', hbd'⟩

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_no_commonNeighbor_of_mem_mem
