import Proofs.Erdos85FinFiveMatchingDomain
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockTwoEdges

/-! Every labeling of an actual H3 special block belongs to the finite matching domain. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_special_internal_matching_domain
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z)
    (e : (↑(G.neighborFinset s ∩ threeHighTripleEmptySet G) : Set (Fin 49)) ≃ Fin 5) :
    oneHighBranchGraphEdges (SimpleGraph.comap e.symm
      (G.induce (↑(G.neighborFinset s ∩ threeHighTripleEmptySet G) : Set (Fin 49)))) ∈
        finFiveTwoEdgeMatchingMasks := by
  classical
  let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let H := G.induce (↑B : Set (Fin 49))
  have hd : ∀ x : (↑B : Set (Fin 49)), H.degree x ≤ 1 :=
    neighbor_block_induce_degree_le_one G hfree s B Finset.inter_subset_left
  have he : H.edgeFinset.card = 2 :=
    threeHigh_triple_special_internal_edges_eq_two G hfree hmin hHigh hone z hz hu huz hs
  exact relabeled_two_edge_graph_mem_matching_masks H e hd he

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_special_internal_matching_domain
