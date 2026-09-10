import Proofs.Erdos85MatchingNestedNormalForm

/-! Exact structural matching decomposition for the six distinguished empty neighbors. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_neighbor_matching_normal_form
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ k, ∃ e : matchingNestedVertices m k ≃ (↑N : Set (Fin 49)),
      ((m = 1 ∧ k = 4) ∨ (m = 2 ∧ k = 2) ∨ (m = 3 ∧ k = 0)) ∧
      ∀ x y, G.Adj (e x).val (e y).val ↔ matchingNestedAdj m k x y := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let H := G.induce (↑N : Set (Fin 49))
  have hdegree : ∀ x, H.degree x ≤ 1 :=
    neighbor_block_induce_degree_le_one G hfree u N Finset.inter_subset_left
  obtain ⟨k, e, hc, he⟩ := finite_matching_nested_normal_form_with_card H hdegree
  have hN : N.card = 6 :=
    (threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz).2.2.2.2.1
  have hNc : Fintype.card (↑N : Set (Fin 49)) = 6 := by simpa using hN
  rw [hNc] at hc
  have hm := threeHigh_triple_secondary_matching_edge_bounds G hfree hmin hHigh hone z hz hu huz
  change 1 ≤ H.edgeFinset.card ∧ H.edgeFinset.card ≤ 3 at hm
  refine ⟨k, e, ?_, he⟩
  change (H.edgeFinset.card = 1 ∧ k = 4) ∨ (H.edgeFinset.card = 2 ∧ k = 2) ∨
    (H.edgeFinset.card = 3 ∧ k = 0)
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_neighbor_matching_normal_form
