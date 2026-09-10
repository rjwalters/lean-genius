import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryEdgeCases

/-! Exact edge decomposition at the two far vertices of the secondary graph. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem neighbor_inter_insert_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) (v x : V) (hv : v ∉ N) :
    (G.neighborFinset x ∩ insert v N).card =
      (G.neighborFinset x ∩ N).card + if G.Adj x v then 1 else 0 := by
  classical
  by_cases ha : G.Adj x v
  · have he : G.neighborFinset x ∩ insert v N = insert v (G.neighborFinset x ∩ N) := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      aesop
    rw [he, Finset.card_insert_of_notMem (by simp [hv]), if_pos ha]
  · have he : G.neighborFinset x ∩ insert v N = G.neighborFinset x ∩ N := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      aesop
    rw [he, if_neg ha, Nat.add_zero]

theorem induced_edges_insert_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) (v : V) (hv : v ∉ N) :
    (G.induce (↑(insert v N) : Set V)).edgeFinset.card =
      (G.induce (↑N : Set V)).edgeFinset.card + (G.neighborFinset v ∩ N).card := by
  classical
  have hnew := sum_internalNeighbor_card_eq_twice_induced_edges G (insert v N)
  have hold := sum_internalNeighbor_card_eq_twice_induced_edges G N
  simp only [Finset.filter_mem_eq_inter] at hnew hold
  rw [Finset.sum_insert hv] at hnew
  simp_rw [neighbor_inter_insert_card G N v _ hv] at hnew
  have hsum : (∑ x ∈ N, if G.Adj x v then 1 else 0) = (G.neighborFinset v ∩ N).card := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp [G.adj_comm, and_comm]
  rw [Finset.sum_add_distrib, hsum, hold, if_neg (G.loopless.irrefl v), Nat.add_zero] at hnew
  omega

theorem induced_edges_insert_two_vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) (v w : V)
    (hv : v ∉ N) (hw : w ∉ N) (hvw : v ≠ w) :
    (G.induce (↑(insert v (insert w N)) : Set V)).edgeFinset.card =
      (G.induce (↑N : Set V)).edgeFinset.card + (G.neighborFinset v ∩ N).card +
      (G.neighborFinset w ∩ N).card + if G.Adj v w then 1 else 0 := by
  classical
  rw [induced_edges_insert_vertex G (insert w N) v (by simp [hvw, hv]),
    induced_edges_insert_vertex G N w hw, neighbor_inter_insert_card G N w v hw]
  omega

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
  (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
  {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
include hfree hmin hHigh hone hz hu huz

theorem threeHigh_triple_far_edge_decomposition
    (v w : Fin 49)
    (hT : (threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) \
      (G.neighborFinset u ∩ threeHighTripleEmptySet G) = {v,w}) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    (G.induce (↑R : Set (Fin 49))).edgeFinset.card =
      (G.induce (↑N : Set (Fin 49))).edgeFinset.card + (G.neighborFinset v ∩ N).card +
      (G.neighborFinset w ∩ N).card + if G.Adj v w then 1 else 0 := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  change R \ N = {v,w} at hT
  change (G.induce (↑R : Set (Fin 49))).edgeFinset.card = _
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hvT : v ∈ R \ N := by rw [hT]; simp
  have hwT : w ∈ R \ N := by rw [hT]; simp
  have hvw : v ≠ w := by
    intro he
    have hc : (R \ N).card = 2 := hp.2.2.2.2.2
    rw [hT, he] at hc
    simp at hc
  have hpart : R = insert v (insert w N) := by
    ext x
    have hNR : N ⊆ R := hp.2.2.2.1
    constructor
    · intro hx
      by_cases hxN : x ∈ N
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxN)
      · have hxT : x ∈ R \ N := Finset.mem_sdiff.mpr ⟨hx, hxN⟩
        rw [hT] at hxT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
        rcases hxT with rfl | rfl <;> simp
    · intro hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact (Finset.mem_sdiff.mp hvT).1
      · exact (Finset.mem_sdiff.mp hwT).1
      · exact hNR hx
  rw [hpart]
  exact induced_edges_insert_two_vertices G N v w (Finset.mem_sdiff.mp hvT).2
    (Finset.mem_sdiff.mp hwT).2 hvw

theorem threeHigh_triple_three_matching_edges_far_rigidity
    (v w : Fin 49)
    (hT : (threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) \
      (G.neighborFinset u ∩ threeHighTripleEmptySet G) = {v,w})
    (hm : (G.induce (↑(G.neighborFinset u ∩ threeHighTripleEmptySet G) : Set (Fin 49))).edgeFinset.card = 3) :
    G.Adj v w ∧
      (G.neighborFinset v ∩ (G.neighborFinset u ∩ threeHighTripleEmptySet G)).card = 0 ∧
      (G.neighborFinset w ∩ (G.neighborFinset u ∩ threeHighTripleEmptySet G)).card = 0 := by
  classical
  have hd := threeHigh_triple_far_edge_decomposition G hfree hmin hHigh hone z hz hu huz v w hT
  have hr := threeHigh_triple_secondary_edges_three_or_four G hfree hmin hHigh hone z hz hu huz
  have hv := threeHigh_triple_far_parameter_lower_bound G hfree hmin hHigh hone z hz hu huz v w hT
  have hw := threeHigh_triple_far_parameter_lower_bound G hfree hmin hHigh hone z hz hu huz w v
    (hT.trans (Finset.pair_comm v w))
  dsimp only at hd hr
  rw [hm] at hd
  simp only [G.adj_comm w v] at hw
  by_cases ha : G.Adj v w
  · rw [if_pos ha] at hd hv hw
    exact ⟨ha, by omega, by omega⟩
  · rw [if_neg ha] at hd hv hw
    omega

end
end Erdos85
#print axioms Erdos85.induced_edges_insert_vertex
#print axioms Erdos85.induced_edges_insert_two_vertices
#print axioms Erdos85.threeHigh_triple_far_edge_decomposition
#print axioms Erdos85.threeHigh_triple_three_matching_edges_far_rigidity
