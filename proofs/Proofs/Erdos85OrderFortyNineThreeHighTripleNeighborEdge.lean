import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition
import Proofs.Erdos85OrderFortyNineLowTriangles

/-! The distinguished empty vertex lies on an empty triangle, forcing m ≥ 1. -/
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

private theorem distinguished_degree_seven {u : Fin 49}
    (hu : u ∈ threeHighTripleEmptySet G) : G.degree u = 7 := by
  have hlow := (Finset.mem_filter.mp hu).1
  rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) u with h | h
  · exact h
  · exact ((Finset.mem_sdiff.mp hlow).2 (by simp [orderFortyNineHighVertices, h])).elim

theorem threeHigh_triple_distinguished_other_neighbor_empty
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {x : Fin 49} (hux : G.Adj u x) (hxz : x ≠ z) :
    x ∈ threeHighTripleEmptySet G := by
  classical
  have hu7 := distinguished_degree_seven G hfree hmin hHigh hone hu
  have hd := orderFortyNine_graphNeighbor_highSupports_pairwiseDisjoint G hfree hmin
    (Fintype.card_fin 49) hu7 ((G.mem_neighborFinset u z).mpr huz)
    ((G.mem_neighborFinset u x).mpr hux) hxz.symm
  have hzH : orderFortyNineHighSupport G z = orderFortyNineHighVertices G :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq (hHigh.trans hz.symm))
  have hx0 : (orderFortyNineHighSupport G x).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hwz : w ∈ orderFortyNineHighSupport G z := by
      rw [hzH]
      exact (Finset.mem_inter.mp hw).2
    exact Finset.disjoint_left.mp hd hwz hw
  have hu0 := (Finset.mem_filter.mp hu).2
  have hxnot : x ∉ orderFortyNineHighVertices G := by
    intro hxH
    have hmem : x ∈ orderFortyNineHighSupport G u :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u x).mpr hux, hxH⟩
    have hempty := Finset.card_eq_zero.mp hu0
    rw [hempty] at hmem
    exact Finset.notMem_empty x hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnot⟩, hx0⟩

theorem threeHigh_triple_distinguished_root_edge_no_triangle
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (x : Fin 49) (hux : G.Adj u x) : ¬ G.Adj z x := by
  intro hzx
  have hxE := threeHigh_triple_distinguished_other_neighbor_empty G hfree hmin hHigh hone
    z hz hu huz hux hzx.ne.symm
  have hc := threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
  change (G.neighborFinset z ∩ threeHighTripleEmptySet G).card = 1 at hc
  have hxm : x ∈ G.neighborFinset z ∩ threeHighTripleEmptySet G :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr hzx, hxE⟩
  have hum : u ∈ G.neighborFinset z ∩ threeHighTripleEmptySet G :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z u).mpr huz.symm, hu⟩
  have hxu := Finset.card_le_one.mp (show (G.neighborFinset z ∩ threeHighTripleEmptySet G).card ≤ 1 by omega)
    x hxm u hum
  exact hux.ne hxu.symm

theorem threeHigh_triple_distinguished_empty_neighbors_have_edge
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    ∃ a ∈ G.neighborFinset u ∩ threeHighTripleEmptySet G,
      ∃ b ∈ G.neighborFinset u ∩ threeHighTripleEmptySet G, G.Adj a b := by
  have hu7 := distinguished_degree_seven G hfree hmin hHigh hone hu
  have hu0 := (Finset.mem_filter.mp hu).2
  obtain ⟨a, b, ha7, hb7, hua, hub, hab⟩ :=
    orderFortyNine_exists_allLow_triangle_of_highNeighborCount_zero
      G hfree hmin (Fintype.card_fin 49) hu7 hu0
  have haz : a ≠ z := by
    intro heq
    subst a
    exact threeHigh_triple_distinguished_root_edge_no_triangle G hfree hmin hHigh hone z hz hu huz b hub hab
  have hbz : b ≠ z := by
    intro heq
    subst b
    exact threeHigh_triple_distinguished_root_edge_no_triangle G hfree hmin hHigh hone z hz hu huz a hua hab.symm
  refine ⟨a, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u a).mpr hua, ?_⟩,
    b, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u b).mpr hub, ?_⟩, hab⟩
  · exact threeHigh_triple_distinguished_other_neighbor_empty G hfree hmin hHigh hone z hz hu huz hua haz
  · exact threeHigh_triple_distinguished_other_neighbor_empty G hfree hmin hHigh hone z hz hu huz hub hbz

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_distinguished_other_neighbor_empty
#print axioms Erdos85.threeHigh_triple_distinguished_root_edge_no_triangle
#print axioms Erdos85.threeHigh_triple_distinguished_empty_neighbors_have_edge
