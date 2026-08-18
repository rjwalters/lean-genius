import Proofs.Erdos85BinarySquareMixedOwnerRootedAllDistinct
import Proofs.Erdos85BinarySquareRoutingStarCompletions

/-! # From rooted all-distinct owner triangles to routing cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Across two distinct defect components, an owner-colored edge is routed
through precisely that owner component. -/
theorem crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x : d.supp) (y : e.supp)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj
      x.1 y.1) :
    crossIntermediateComponent G hfree hde x y = owner := by
  rw [componentOwnerGraph_adj] at howner
  obtain ⟨_hxy, u, hu⟩ := howner
  have hu' := Finset.mem_inter.mp hu
  have hux := Finset.mem_filter.mp hu'.1
  have huy := Finset.mem_filter.mp hu'.2
  calc
    crossIntermediateComponent G hfree hde x y =
        (secondOrderDefectGraph G).connectedComponentMk u :=
      crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
        G hfree hde x y
          ⟨(G.mem_neighborFinset x.1 u).mp hux.1,
            (G.mem_neighborFinset y.1 u).mp huy.1⟩
    _ = owner := hux.2

/-- Conversely, specifying the routing component gives the corresponding
owner-colored edge. -/
theorem componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x : d.supp) (y : e.supp)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hroute : crossIntermediateComponent G hfree hde x y = owner) :
    (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x.1 y.1 := by
  obtain ⟨u, hu, _huniq⟩ := crossIntermediateComponent_spec G hfree hde x y
  have hxy : x.1 ≠ y.1 := by
    intro h
    apply hde
    have hx := (ConnectedComponent.mem_supp_iff d x.1).mp x.2
    have hy := (ConnectedComponent.mem_supp_iff e y.1).mp y.2
    exact hx.symm.trans (by simpa [h] using hy)
  rw [componentOwnerGraph_adj]
  refine ⟨hxy, u.1, ?_⟩
  have hucomp : (secondOrderDefectGraph G).connectedComponentMk u.1 = owner := by
    have := (ConnectedComponent.mem_supp_iff
      (crossIntermediateComponent G hfree hde x y) u.1).mp u.2
    simpa [hroute] using this
  simp only [Finset.mem_inter, componentNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset]
  exact ⟨⟨hu.1, hucomp⟩, ⟨hu.2, hucomp⟩⟩

/-- Endpoint pairs `(z,y)` which, together with root `x`, occupy three
distinct defect components and whose three cross routes are `a,b,c`. -/
def rootedAllDistinctRoutingCyclePairs
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64) : Finset (Fin 64 × Fin 64) := by
  classical
  let D := secondOrderDefectGraph G
  exact Finset.univ.filter fun p =>
    ∃ (hxy : D.connectedComponentMk x ≠ D.connectedComponentMk p.2)
      (hyz : D.connectedComponentMk p.2 ≠ D.connectedComponentMk p.1)
      (hzx : D.connectedComponentMk p.1 ≠ D.connectedComponentMk x),
      crossIntermediateComponent G hfree hxy
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩ = a ∧
      crossIntermediateComponent G hfree hyz
        ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩ = b ∧
      crossIntermediateComponent G hfree hzx
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩ = c

set_option maxRecDepth 10000 in
/-- Every rooted pattern-four owner triangle is an `(a,b,c)` routing cycle. -/
theorem rootedPattern_four_subset_rootedAllDistinctRoutingCyclePairs
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64) :
    rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4 ⊆
        rootedAllDistinctRoutingCyclePairs G hfree a b c x := by
  classical
  intro p hp
  let D := secondOrderDefectGraph G
  have hpattern := (rootedComponentPattern_eq_four_iff D x p).mp
    (Finset.mem_filter.mp hp).2
  have hcolor := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hxy : D.connectedComponentMk x ≠ D.connectedComponentMk p.2 :=
    hpattern.1.symm
  have hyz : D.connectedComponentMk p.2 ≠ D.connectedComponentMk p.1 :=
    hpattern.2.2
  have hzx : D.connectedComponentMk p.1 ≠ D.connectedComponentMk x :=
    hpattern.2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hxy, hyz, hzx, ?_, ?_, ?_⟩
  · exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hxy
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩ a hcolor.1
  · exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hyz
        ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩ b hcolor.2.1
  · exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hzx
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩ c hcolor.2.2

set_option maxRecDepth 10000 in
/-- The translation is exact: the all-three-distinct owner-triangle finset is
literally the rooted routing-cycle finset. -/
theorem rootedPattern_four_eq_rootedAllDistinctRoutingCyclePairs
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64) :
    rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4 =
        rootedAllDistinctRoutingCyclePairs G hfree a b c x := by
  apply Finset.Subset.antisymm
  · exact rootedPattern_four_subset_rootedAllDistinctRoutingCyclePairs
      G hfree a b c x
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hxy, hyz, hzx, ha, hb, hc⟩ := hp'.2
    let D := secondOrderDefectGraph G
    apply Finset.mem_filter.mpr
    refine ⟨?_, (rootedComponentPattern_eq_four_iff D x p).mpr
      ⟨hxy.symm, hzx, hyz⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
        G hfree hxy
          ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
          ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩ a ha
    · exact componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
        G hfree hyz
          ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩
          ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩ b hb
    · exact componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
        G hfree hzx
          ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩
          ⟨x, ConnectedComponent.connectedComponentMk_mem⟩ c hc

/-- At order 64, every root supports at least twelve `(a,b,c)` routing
cycles for every ordered triple of distinct owner colors. -/
theorem orderSixtyFour_regular_fourComponents_rootedAllDistinctRoutingCyclePairs_card_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Fin 64) :
    12 ≤ (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card := by
  have hsub := rootedPattern_four_subset_rootedAllDistinctRoutingCyclePairs
    G hfree a b c x
  have hle := Finset.card_le_card hsub
  have hpattern :=
    orderSixtyFour_regular_fourComponents_rootedPattern_four_card_ge_twelve
      G hfree hreg hcount a b c hab hac hbc x
  omega

end

end Erdos85
