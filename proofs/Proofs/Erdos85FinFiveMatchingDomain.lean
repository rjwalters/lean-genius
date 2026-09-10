import Proofs.Erdos85FinFiveMatchingKernel

/-! Exact kernel-checked domain of the fifteen two-edge matchings on Fin 5. -/
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
namespace Erdos85
open SimpleGraph

def finFiveTwoEdgeMatchingMasks : Finset (BitVec 10) :=
  {129, 257, 513, 34, 66, 514, 20, 68, 260, 24, 40, 136, 528, 288, 192}

theorem finFiveTwoEdgeMatchingMasks_card : finFiveTwoEdgeMatchingMasks.card = 15 := by
  decide

theorem finFiveTwoEdgeMatchingMasks_mem_iff (bits : BitVec 10) :
    bits ∈ finFiveTwoEdgeMatchingMasks ↔
      (∀ i : Fin 5, (Finset.univ.filter fun j => oneHighBranchBitAdj bits i j).card ≤ 1) ∧
      (Finset.univ.filter fun i =>
        (Finset.univ.filter fun j => oneHighBranchBitAdj bits i j).card = 1).card = 4 := by
  decide +revert

theorem finFive_two_edge_graph_mem_matching_masks
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj]
    (hdegree : ∀ x, H.degree x ≤ 1) (hedges : H.edgeFinset.card = 2) :
    oneHighBranchGraphEdges H ∈ finFiveTwoEdgeMatchingMasks := by
  classical
  have hrow (i : Fin 5) :
      (Finset.univ.filter fun j => oneHighBranchBitAdj (oneHighBranchGraphEdges H) i j) =
        H.neighborFinset i := by
    ext j
    simp [oneHighBranchBitAdj_graphEdges_kernel, SimpleGraph.mem_neighborFinset]
  apply (finFiveTwoEdgeMatchingMasks_mem_iff _).mpr
  constructor
  · intro i
    rw [hrow, H.card_neighborFinset_eq_degree]
    exact hdegree i
  · have hsum : (∑ x : Fin 5, H.degree x) =
        (Finset.univ.filter fun x => H.degree x = 1).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      have hd := hdegree x
      split_ifs <;> omega
    have hm : (Finset.univ.filter fun x => H.degree x = 1).card = 4 := by
      rw [← hsum, SimpleGraph.sum_degrees_eq_twice_card_edges, hedges]
    simpa only [hrow, H.card_neighborFinset_eq_degree] using hm

/-- Every labeling of a five-point two-edge matching lands in the same
fifteen-mask domain. -/
theorem relabeled_two_edge_graph_mem_matching_masks
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : SimpleGraph P) [DecidableRel H.Adj] (e : P ≃ Fin 5)
    (hdegree : ∀ x, H.degree x ≤ 1) (hedges : H.edgeFinset.card = 2) :
    oneHighBranchGraphEdges (SimpleGraph.comap e.symm H) ∈ finFiveTwoEdgeMatchingMasks := by
  classical
  let R := SimpleGraph.comap e.symm H
  have hd : ∀ i, R.degree i ≤ 1 := by
    intro i
    have hi := (SimpleGraph.Iso.comap e.symm H).degree_eq i
    exact hi.symm.trans_le (hdegree (e.symm i))
  have he : R.edgeFinset.card = 2 := by
    have hi := (SimpleGraph.Iso.comap e.symm H).card_edgeFinset_eq
    exact hi.trans hedges
  exact finFive_two_edge_graph_mem_matching_masks R hd he

end Erdos85
#print axioms Erdos85.finFiveTwoEdgeMatchingMasks_card
#print axioms Erdos85.finFiveTwoEdgeMatchingMasks_mem_iff
#print axioms Erdos85.finFive_two_edge_graph_mem_matching_masks

#print axioms Erdos85.relabeled_two_edge_graph_mem_matching_masks
