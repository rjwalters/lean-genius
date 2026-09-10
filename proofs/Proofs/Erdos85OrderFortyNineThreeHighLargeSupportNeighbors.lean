import Proofs.Erdos85OrderFortyNineSupportPartitions

/-! Large high supports cannot share a low neighbor in the H3 stratum. -/
namespace Erdos85
open SimpleGraph
noncomputable section

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)

include hfree hmin hHigh

theorem threeHigh_large_support_neighbors_eq
    {v x y : Fin 49} (hv : G.degree v = 7)
    (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v)
    (hsx : 2 ≤ (orderFortyNineHighSupport G x).card)
    (hsy : 2 ≤ (orderFortyNineHighSupport G y).card) : x = y := by
  by_contra hne
  have hd := orderFortyNine_graphNeighbor_highSupports_pairwiseDisjoint
    G hfree hmin (Fintype.card_fin 49) hv hx hy hne
  have hsub : orderFortyNineHighSupport G x ∪ orderFortyNineHighSupport G y ⊆
      orderFortyNineHighVertices G := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_inter.mp hw).2
    · exact (Finset.mem_inter.mp hw).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hHigh] at hc
  omega

theorem threeHigh_large_support_neighbor_count_le_one
    {v : Fin 49} (hv : G.degree v = 7) :
    ((G.neighborFinset v).filter fun x =>
      2 ≤ (orderFortyNineHighSupport G x).card).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact threeHigh_large_support_neighbors_eq G hfree hmin hHigh hv
    (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

theorem threeHigh_large_support_low_neighborhoods_disjoint
    {x y : Fin 49} (hxy : x ≠ y)
    (hsx : 2 ≤ (orderFortyNineHighSupport G x).card)
    (hsy : 2 ≤ (orderFortyNineHighSupport G y).card) :
    Disjoint ((G.neighborFinset x).filter fun v => G.degree v = 7)
      ((G.neighborFinset y).filter fun v => G.degree v = 7) := by
  apply Finset.disjoint_left.mpr
  intro v hx hy
  have h := threeHigh_large_support_neighbors_eq G hfree hmin hHigh
    (Finset.mem_filter.mp hx).2
    (by simpa only [SimpleGraph.mem_neighborFinset, G.adj_comm] using (Finset.mem_filter.mp hx).1)
    (by simpa only [SimpleGraph.mem_neighborFinset, G.adj_comm] using (Finset.mem_filter.mp hy).1)
    hsx hsy
  exact hxy h

end
end Erdos85
#print axioms Erdos85.threeHigh_large_support_neighbors_eq
#print axioms Erdos85.threeHigh_large_support_neighbor_count_le_one
#print axioms Erdos85.threeHigh_large_support_low_neighborhoods_disjoint
