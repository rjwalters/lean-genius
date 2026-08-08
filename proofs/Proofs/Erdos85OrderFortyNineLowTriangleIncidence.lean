import Proofs.Erdos85OrderFortyNineLowTriangles

/-!
# High-incidence separation on all-low triangles

The endpoints of an edge in an all-low triangle cannot share a high
neighbor, since that high vertex and the third triangle vertex would be two
distinct common neighbors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two low endpoints of an edge with a low common neighbor have disjoint
sets of high neighbors. -/
theorem orderFortyNine_disjoint_highNeighbors_of_allLow_triangle_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y z : V} (hx : G.degree x = 7) (hy : G.degree y = 7)
    (hz : G.degree z = 7) (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    Disjoint
      (G.neighborFinset x ∩ orderFortyNineHighVertices G)
      (G.neighborFinset y ∩ orderFortyNineHighVertices G) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  have hv8 : G.degree v = 8 :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hvx).2).2
  have hvxAdj : G.Adj v x := by
    have := (Finset.mem_inter.mp hvx).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hvyAdj : G.Adj v y := by
    have := (Finset.mem_inter.mp hvy).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hvzne : v ≠ z := by
    intro hvz
    subst z
    omega
  exact hfree (containsC4_of_two_common hxyne hvzne
    hvxAdj hvyAdj hxz.symm hyz.symm)

/-- The three high-incidence blocks on an all-low triangle are pairwise
disjoint. -/
theorem orderFortyNine_pairwiseDisjoint_highNeighbors_of_allLow_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y z : V} (hx : G.degree x = 7) (hy : G.degree y = 7)
    (hz : G.degree z = 7) (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    Disjoint
        (G.neighborFinset x ∩ orderFortyNineHighVertices G)
        (G.neighborFinset y ∩ orderFortyNineHighVertices G) ∧
      Disjoint
        (G.neighborFinset x ∩ orderFortyNineHighVertices G)
        (G.neighborFinset z ∩ orderFortyNineHighVertices G) ∧
      Disjoint
        (G.neighborFinset y ∩ orderFortyNineHighVertices G)
        (G.neighborFinset z ∩ orderFortyNineHighVertices G) := by
  exact ⟨
    orderFortyNine_disjoint_highNeighbors_of_allLow_triangle_edge
      G hfree hx hy hz hxy hxz hyz,
    orderFortyNine_disjoint_highNeighbors_of_allLow_triangle_edge
      G hfree hx hz hy hxz hxy hyz.symm,
    orderFortyNine_disjoint_highNeighbors_of_allLow_triangle_edge
      G hfree hy hz hx hyz hxy.symm hxz.symm⟩

/-- Consequently the total high incidence carried by the three vertices of
an all-low triangle is at most the number of high vertices. -/
theorem orderFortyNine_sum_highNeighborCount_allLow_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y z : V} (hx : G.degree x = 7) (hy : G.degree y = 7)
    (hz : G.degree z = 7) (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card +
        (G.neighborFinset y ∩ orderFortyNineHighVertices G).card +
        (G.neighborFinset z ∩ orderFortyNineHighVertices G).card ≤
      (orderFortyNineHighVertices G).card := by
  let X := G.neighborFinset x ∩ orderFortyNineHighVertices G
  let Y := G.neighborFinset y ∩ orderFortyNineHighVertices G
  let Z := G.neighborFinset z ∩ orderFortyNineHighVertices G
  rcases orderFortyNine_pairwiseDisjoint_highNeighbors_of_allLow_triangle
    G hfree hx hy hz hxy hxz hyz with ⟨hXY, hXZ, hYZ⟩
  change Disjoint X Y at hXY
  change Disjoint X Z at hXZ
  change Disjoint Y Z at hYZ
  have hXYZ : Disjoint (X ∪ Y) Z :=
    Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  have hsub : X ∪ Y ∪ Z ⊆ orderFortyNineHighVertices G := by
    intro v hv
    simp only [Finset.mem_union, X, Y, Z, Finset.mem_inter] at hv
    rcases hv with (⟨_, hv⟩ | ⟨_, hv⟩) | ⟨_, hv⟩ <;> exact hv
  calc
    X.card + Y.card + Z.card = (X ∪ Y ∪ Z).card := by
      rw [Finset.card_union_of_disjoint hXYZ,
        Finset.card_union_of_disjoint hXY]
    _ ≤ (orderFortyNineHighVertices G).card := Finset.card_le_card hsub

end

end Erdos85
