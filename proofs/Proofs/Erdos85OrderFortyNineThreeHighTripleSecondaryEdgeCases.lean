import Proofs.Erdos85OrderFortyNineThreeHighTripleEdgeLedger
import Proofs.Erdos85OrderFortyNineThreeHighTripleUnionEdges

/-! Actual triple-profile secondary edge counts and cut sizes. -/
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
  (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
  {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)

include hfree hmin hHigh hone hz hu huz

theorem threeHigh_triple_secondary_edges_three_or_four :
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    (G.induce (↑R : Set (Fin 49))).edgeFinset.card = 3 ∨
      (G.induce (↑R : Set (Fin 49))).edgeFinset.card = 4 := by
  classical
  have hl := threeHigh_triple_union_secondary_edge_ledger G hfree hmin hHigh hone z hz hu huz
  have hc := threeHigh_triple_special_union_edges_twenty_or_twentyOne G hfree hmin hHigh hone z hz hu huz
  dsimp only at hl hc ⊢
  omega

theorem threeHigh_triple_secondary_edge_cut_cases :
    let U := threeHighTripleSpecialUnion G z
    let R := threeHighTripleEmptySet G \ insert u U
    let q := ∑ x ∈ U, (G.neighborFinset x ∩ R).card
    ((G.induce (↑R : Set (Fin 49))).edgeFinset.card = 3 ∧ q = 20) ∨
      ((G.induce (↑R : Set (Fin 49))).edgeFinset.card = 4 ∧ q = 18) := by
  classical
  have hl := threeHigh_triple_union_secondary_edge_ledger G hfree hmin hHigh hone z hz hu huz
  have hc := threeHigh_triple_secondary_edges_three_or_four G hfree hmin hHigh hone z hz hu huz
  dsimp only at hl hc ⊢
  omega

theorem threeHigh_triple_matching_edges_lt_secondary_edges :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    (G.induce (↑N : Set (Fin 49))).edgeFinset.card <
      (G.induce (↑R : Set (Fin 49))).edgeFinset.card := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  change (G.induce (↑N : Set (Fin 49))).edgeFinset.card <
    (G.induce (↑R : Set (Fin 49))).edgeFinset.card
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hNR : N ⊆ R := hp.2.2.2.1
  have hT : (R \ N).card = 2 := hp.2.2.2.2.2
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (R \ N).card by omega)
  obtain ⟨w, hw, hvw⟩ :=
    threeHigh_triple_far_vertex_has_secondary_neighbor G hfree hmin hHigh hone z hz hu huz hv
  have hvpos : 0 < (G.neighborFinset v ∩ R).card := by
    exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, hw⟩⟩
  have hle : (∑ x ∈ N, (G.neighborFinset x ∩ N).card) ≤
      ∑ x ∈ N, (G.neighborFinset x ∩ R).card := by
    apply Finset.sum_le_sum
    intro x hx
    exact Finset.card_le_card (Finset.inter_subset_inter_left hNR)
  have hlt : (∑ x ∈ N, (G.neighborFinset x ∩ R).card) <
      ∑ x ∈ R, (G.neighborFinset x ∩ R).card :=
    Finset.sum_lt_sum_of_subset hNR (Finset.mem_sdiff.mp hv).1
      (Finset.mem_sdiff.mp hv).2 hvpos (fun _ _ _ => Nat.zero_le _)
  have hn := sum_internalNeighbor_card_eq_twice_induced_edges G N
  have hr := sum_internalNeighbor_card_eq_twice_induced_edges G R
  simp only [Finset.filter_mem_eq_inter] at hn hr
  omega

theorem threeHigh_triple_matching_secondary_five_cases :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    let r := (G.induce (↑R : Set (Fin 49))).edgeFinset.card
    (m = 1 ∧ r = 3) ∨ (m = 1 ∧ r = 4) ∨
      (m = 2 ∧ r = 3) ∨ (m = 2 ∧ r = 4) ∨ (m = 3 ∧ r = 4) := by
  classical
  have hm := threeHigh_triple_secondary_matching_edge_bounds G hfree hmin hHigh hone z hz hu huz
  have hr := threeHigh_triple_secondary_edges_three_or_four G hfree hmin hHigh hone z hz hu huz
  have hlt := threeHigh_triple_matching_edges_lt_secondary_edges G hfree hmin hHigh hone z hz hu huz
  dsimp only at hm hr hlt ⊢
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_edges_three_or_four
#print axioms Erdos85.threeHigh_triple_secondary_edge_cut_cases

#print axioms Erdos85.threeHigh_triple_matching_edges_lt_secondary_edges
#print axioms Erdos85.threeHigh_triple_matching_secondary_five_cases
