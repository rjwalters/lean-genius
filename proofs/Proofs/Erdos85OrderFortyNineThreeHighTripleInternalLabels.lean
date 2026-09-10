import Proofs.Erdos85FinFiveMatchingKernel
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockTwoEdges

/-! Canonical internal matching labels for an actual H3 special block. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_special_internal_matching_labels
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
    ∃ e : (↑B : Set (Fin 49)) ≃ Fin 5,
      ∀ x y, decide (G.Adj x.val y.val) =
        oneHighCanonicalBranchAdj true (e x) (e y) := by
  classical
  let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let H := G.induce (↑B : Set (Fin 49))
  have hs1 := (Finset.mem_filter.mp hs).2
  have hsz := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm
  have hc : B.card = 5 :=
    threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs1 hsz
  have hP : Fintype.card (↑B : Set (Fin 49)) = 5 := by simpa using hc
  have hd : ∀ x : (↑B : Set (Fin 49)), H.degree x ≤ 1 :=
    neighbor_block_induce_degree_le_one G hfree s B Finset.inter_subset_left
  have he : H.edgeFinset.card = 2 :=
    threeHigh_triple_special_internal_edges_eq_two G hfree hmin hHigh hone z hz hu huz hs
  obtain ⟨e,he⟩ := exists_equiv_finFive_two_edge_matching H hP hd he
  exact ⟨e,he⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_special_internal_matching_labels
