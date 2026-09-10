import Proofs.Erdos85MatchingFinSixCoordinates
import Proofs.Erdos85OrderFortyNineThreeHighTripleNeighborNormalForm

/-! Exact consecutive matching labels on the six distinguished empty neighbors. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_neighbor_matching_coordinates
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
    ∃ e : Fin 6 ≃ (↑N : Set (Fin 49)),
      1 ≤ m ∧ m ≤ 3 ∧ ∀ i j, G.Adj (e i).val (e j).val ↔ matchingFinSixAdj m i j := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let H := G.induce (↑N : Set (Fin 49))
  obtain ⟨k, e, hc, he⟩ := threeHigh_triple_neighbor_matching_normal_form
    G hfree hmin hHigh hone z hz hu huz
  obtain ⟨f, hf⟩ := matching_nested_six_coordinates hc
  let l : Fin 6 ≃ (↑N : Set (Fin 49)) := f.symm.trans e
  have hm := threeHigh_triple_secondary_matching_edge_bounds G hfree hmin hHigh hone z hz hu huz
  refine ⟨l, hm.1, hm.2, ?_⟩
  intro i j
  change G.Adj (e (f.symm i)).val (e (f.symm j)).val ↔ _
  exact (he _ _).trans (hf i j)

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_neighbor_matching_coordinates
