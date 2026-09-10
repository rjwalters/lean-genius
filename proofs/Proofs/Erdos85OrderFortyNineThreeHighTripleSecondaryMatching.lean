import Proofs.Erdos85OrderFortyNineThreeHighTripleNeighborEdge
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockCapacity

/-! Actual matching parameter bounds in the triple-profile secondary set. -/
namespace Erdos85
open SimpleGraph
noncomputable section
variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
include hfree hmin hHigh hone

theorem threeHigh_triple_secondary_matching_edge_bounds
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    1 ≤ (G.induce (↑N : Set (Fin 49))).edgeFinset.card ∧
      (G.induce (↑N : Set (Fin 49))).edgeFinset.card ≤ 3 := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let A := G.induce (↑N : Set (Fin 49))
  change 1 ≤ A.edgeFinset.card ∧ A.edgeFinset.card ≤ 3
  have hN : N.card = 6 :=
    (threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz).2.2.2.2.1
  have hupper := neighbor_block_twice_edges_le_card G hfree u N Finset.inter_subset_left
  have hlower : 0 < A.edgeFinset.card := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      threeHigh_triple_distinguished_empty_neighbors_have_edge G hfree hmin hHigh hone z hz hu huz
    apply Finset.card_pos.mpr
    refine ⟨s((⟨a, ha⟩ : (↑N : Set (Fin 49))), (⟨b, hb⟩ : (↑N : Set (Fin 49)))), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hab
  change 2 * A.edgeFinset.card ≤ N.card at hupper
  rw [hN] at hupper
  omega

theorem threeHigh_triple_secondary_matching_degree_le_one
    (u : Fin 49) (x : (↑(G.neighborFinset u ∩ threeHighTripleEmptySet G) : Set (Fin 49))) :
    (G.induce (↑(G.neighborFinset u ∩ threeHighTripleEmptySet G) : Set (Fin 49))).degree x ≤ 1 := by
  exact neighbor_block_induce_degree_le_one G hfree u _ Finset.inter_subset_left x

theorem threeHigh_triple_secondary_vertex_neighbor_bound
    (z : Fin 49) (u : Fin 49)
    {v : Fin 49}
    (hv : v ∈ threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
    (G.neighborFinset v ∩ (G.neighborFinset u ∩ threeHighTripleEmptySet G)).card ≤ 1 := by
  have hvu : v ≠ u := by
    intro heq
    subst v
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_insert_self _ _)
  exact neighbor_block_inter_card_le_one G hfree u _ Finset.inter_subset_left hvu

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_matching_edge_bounds
#print axioms Erdos85.threeHigh_triple_secondary_matching_degree_le_one
#print axioms Erdos85.threeHigh_triple_secondary_vertex_neighbor_bound
