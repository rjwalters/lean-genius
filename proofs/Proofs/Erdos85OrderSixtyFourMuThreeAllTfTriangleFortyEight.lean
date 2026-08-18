import Proofs.Erdos85OrderSixtyFourTriangleFreeColorOrder
import Proofs.Erdos85MuThreeComponentTriangleFortyEight
import Proofs.Erdos85RootedTriangleCyclicCount

/-!
# The graph-facing 48 count for an all-triangle-free size-sixteen component

This file connects the abstract local triangle count to the order-64
second-order defect-component model.  If every vertex of a size-sixteen
component has triangle-free degree two, its two internal ambient neighbours
are exactly its triangle-free neighbours.  Consequently the component roots
exactly 48 triangles, and both non-root vertices of every such triangle lie
outside the component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In an all-triangle-free size-sixteen defect component, every ambient
neighbour that remains in the component is a triangle-free neighbour. -/
theorem orderSixtyFour_allSixteen_tfComponent_internal_neighbor_triangleFree
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = 16)
    (htf : ∀ x : c.supp, (triangleFreeEdgeGraph G).degree x.1 = 2)
    (x : c.supp) {y : Fin 64} (hxy : G.Adj x.1 y) (hy : y ∈ c.supp) :
    y ∈ triangleFreeNeighbors G x.1 := by
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  have htarget : (componentNeighborFinset G D c x.1).card = 2 := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
      c c (x := x.1) x.2
    rw [hsize] at hmul
    have hcard :
        (componentNeighborFinset G (secondOrderDefectGraph G) c x.1).card = 2 := by
      omega
    simpa [D] using hcard
  have hsub : T.neighborFinset x.1 ⊆ componentNeighborFinset G D c x.1 := by
    intro z hz
    have hTxz : T.Adj x.1 z := (T.mem_neighborFinset x.1 z).mp hz
    have hDxz : D.Adj x.1 z := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 z
      exact Or.inr hTxz
    rw [componentNeighborFinset, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact (G.mem_neighborFinset x.1 z).mpr
        (((mem_triangleFreeNeighbors G x.1 z).mp
          ((triangleFreeEdgeGraph_adj G x.1 z).mp hTxz)).1)
    · rw [← ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.mem_supp_congr_adj c hDxz).mp x.2
  have hTeq : T.neighborFinset x.1 = componentNeighborFinset G D c x.1 := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [T.card_neighborFinset_eq_degree, htf x, htarget]
  have hyTarget : y ∈ componentNeighborFinset G D c x.1 := by
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset x.1 y).mpr hxy,
      (ConnectedComponent.mem_supp_iff c y).mp hy⟩
  have hTxy : T.Adj x.1 y := by
    exact (T.mem_neighborFinset x.1 y).mp (hTeq.symm ▸ hyTarget)
  exact (triangleFreeEdgeGraph_adj G x.1 y).mp hTxy

/-- **Graph-facing exact 48.**  An all-triangle-free size-sixteen defect
component at the order-64 degree-eight boundary roots exactly 48 triangles. -/
theorem orderSixtyFour_allSixteen_tfComponent_sum_localTriangleEdges_eq_fortyEight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = 16)
    (htf : ∀ x : c.supp, (triangleFreeEdgeGraph G).degree x.1 = 2) :
    (∑ x : c.supp,
      (G.induce (G.neighborSet x.1)).edgeFinset.card) = 48 := by
  apply sum_localTriangleEdges_eq_fortyEight_of_card_sixteen_degree_eight_tf_two
    G hfree c.supp
  · simpa [Nat.card_eq_fintype_card] using
      (Nat.card_coe_set_eq c.supp).trans hsize
  · intro x
    exact hreg x.1
  · intro x
    rw [← triangleFreeEdgeGraph_neighborFinset,
      (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, htf x]

/-- The oriented form of the exact 48 count: fixing the component vertex as
the first root gives exactly 96 ordered closing pairs. -/
theorem orderSixtyFour_allSixteen_tfComponent_sum_rootedCyclicPairs_eq_ninetySix
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = 16)
    (htf : ∀ x : c.supp, (triangleFreeEdgeGraph G).degree x.1 = 2) :
    (∑ x : c.supp, (rootedCyclicColoredPairs G G G x.1).card) = 96 := by
  have hfortyEight :=
    orderSixtyFour_allSixteen_tfComponent_sum_localTriangleEdges_eq_fortyEight
      G hfree hreg c hsize htf
  calc
    (∑ x : c.supp, (rootedCyclicColoredPairs G G G x.1).card) =
        ∑ x : c.supp,
          2 * (G.induce (G.neighborSet x.1)).edgeFinset.card := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact card_rootedCyclicColoredPairs_self_eq_two_mul_localTriangleEdges
        G x.1
    _ = 2 * (∑ x : c.supp,
          (G.induce (G.neighborSet x.1)).edgeFinset.card) := by
      rw [Finset.mul_sum]
    _ = 96 := by rw [hfortyEight]

/-- Every triangle rooted in an all-triangle-free size-sixteen defect
component has its other two vertices outside that component. -/
theorem orderSixtyFour_allSixteen_tfComponent_rooted_triangle_endpoints_exterior
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = 16)
    (htf : ∀ x : c.supp, (triangleFreeEdgeGraph G).degree x.1 = 2)
    (x : c.supp) {y z : Fin 64}
    (hxy : G.Adj x.1 y) (hxz : G.Adj x.1 z) (hyz : G.Adj y z) :
    y ∉ c.supp ∧ z ∉ c.supp := by
  apply rooted_triangle_endpoints_not_mem_of_internal_neighbors_triangleFree
    G c.supp
    (orderSixtyFour_allSixteen_tfComponent_internal_neighbor_triangleFree
      G hfree hreg c hsize htf)
    x hxy hxz hyz

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_allSixteen_tfComponent_internal_neighbor_triangleFree
#print axioms
  Erdos85.orderSixtyFour_allSixteen_tfComponent_sum_localTriangleEdges_eq_fortyEight
#print axioms
  Erdos85.orderSixtyFour_allSixteen_tfComponent_sum_rootedCyclicPairs_eq_ninetySix
#print axioms
  Erdos85.orderSixtyFour_allSixteen_tfComponent_rooted_triangle_endpoints_exterior
