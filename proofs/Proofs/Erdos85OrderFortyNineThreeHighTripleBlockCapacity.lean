import Proofs.Erdos85OrderFortyNineThreeHighTripleSpecialBlocks

/-! C4-free capacity bounds for the actual five-vertex special blocks. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem neighbor_block_inter_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : V) (B : Finset V)
    (hB : B ⊆ G.neighborFinset s) {x : V} (hxs : x ≠ s) :
    (G.neighborFinset x ∩ B).card ≤ 1 := by
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree x s hxs
  exact (Finset.card_le_card (Finset.inter_subset_inter_left hB)).trans hc

theorem neighbor_block_incidence_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : V) (B W : Finset V)
    (hB : B ⊆ G.neighborFinset s) (hs : s ∉ W) :
    (∑ x ∈ W, (G.neighborFinset x ∩ B).card) ≤ W.card := by
  calc
    _ ≤ ∑ _x ∈ W, 1 := Finset.sum_le_sum (fun x hx =>
      neighbor_block_inter_card_le_one G hfree s B hB (by intro h; subst x; exact hs hx))
    _ = W.card := by simp

private theorem induce_neighbor_card_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V)
    (x : (↑B : Set V)) :
    ((G.induce (↑B : Set V)).neighborFinset x).card =
      (G.neighborFinset x.val ∩ B).card := by
  classical
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (((G.induce (↑B : Set V)).mem_neighborFinset _ _).mp hy), y.property⟩
  · intro y hy z hz h
    exact Subtype.ext h
  · intro y hy
    refine ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, ?_, rfl⟩
    exact ((G.induce (↑B : Set V)).mem_neighborFinset _ _).mpr
      ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hy).1)

theorem neighbor_block_induce_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : V) (B : Finset V)
    (hB : B ⊆ G.neighborFinset s) (x : (↑B : Set V)) :
    (G.induce (↑B : Set V)).degree x ≤ 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, induce_neighbor_card_inter]
  apply neighbor_block_inter_card_le_one G hfree s B hB
  exact ((G.mem_neighborFinset _ _).mp (hB x.property)).ne.symm

theorem neighbor_block_twice_edges_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : V) (B : Finset V)
    (hB : B ⊆ G.neighborFinset s) :
    2 * (G.induce (↑B : Set V)).edgeFinset.card ≤ B.card := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc
    _ ≤ ∑ _x : (↑B : Set V), 1 := Finset.sum_le_sum (fun x _ =>
      neighbor_block_induce_degree_le_one G hfree s B hB x)
    _ = B.card := by simp

theorem threeHigh_triple_special_internal_edges_le_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s : Fin 49} (hs : (orderFortyNineHighSupport G s).card = 1)
    (hsz : G.Adj s z) :
    let B := G.neighborFinset s ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)
    (G.induce (↑B : Set (Fin 49))).edgeFinset.card ≤ 2 := by
  classical
  dsimp only
  have hc := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs hsz
  have hb := neighbor_block_twice_edges_le_card G hfree s
    (G.neighborFinset s ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)) Finset.inter_subset_left
  omega

/-- Any five-vertex special block sends at most five incidences to another
special block, since the latter's root has positive support. -/
theorem threeHigh_triple_special_cross_incidence_le_five
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (s t : Fin 49) (hs : (orderFortyNineHighSupport G s).card = 1)
    (ht : (orderFortyNineHighSupport G t).card = 1) (htz : G.Adj t z) :
    let E := (orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0
    (∑ x ∈ G.neighborFinset t ∩ E,
      (G.neighborFinset x ∩ (G.neighborFinset s ∩ E)).card) ≤ 5 := by
  classical
  dsimp only
  have hc := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz ht htz
  have hn : s ∉ G.neighborFinset t ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0) := by
    intro hm
    have hh := (Finset.mem_filter.mp (Finset.mem_inter.mp hm).2).2
    omega
  exact (neighbor_block_incidence_le_card G hfree s _ _ Finset.inter_subset_left hn).trans_eq hc

end
end Erdos85
#print axioms Erdos85.neighbor_block_inter_card_le_one
#print axioms Erdos85.neighbor_block_incidence_le_card
#print axioms Erdos85.neighbor_block_induce_degree_le_one
#print axioms Erdos85.neighbor_block_twice_edges_le_card
#print axioms Erdos85.threeHigh_triple_special_internal_edges_le_two

#print axioms Erdos85.threeHigh_triple_special_cross_incidence_le_five
