import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85BinarySquareRegularParity

/-! # Mixed-owner rectangles route cell by cell

For two distinct owner components, every pair consisting of an `a`-center
at the left root and a `b`-center at the right root determines a unique
mixed-owner middle.  This is the combinatorial realization of the full
`m_a m_b` matrix entry, and requires neither regularity nor square order.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A displayed common neighbor in a component certifies the corresponding
owner color. -/
theorem componentOwnerGraph_adj_of_commonNeighbor_mem_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x y u : V}
    (hxy : x ≠ y) (hu : u ∈ owner.supp)
    (hxu : G.Adj x u) (hyu : G.Adj y u) :
    (componentOwnerGraph G D owner).Adj x y := by
  rw [componentOwnerGraph_adj]
  refine ⟨hxy, ?_⟩
  refine ⟨u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      hxu, (ConnectedComponent.mem_supp_iff owner u).mp hu]
  · simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      hyu, (ConnectedComponent.mem_supp_iff owner u).mp hu]

/-- Every cell of a mixed owner-center rectangle has a unique routing
middle.  The hypotheses excluding owner `a` and owner `b` from the root
pair are exactly what prevent the middle from collapsing to an endpoint. -/
theorem mixedOwnerRectangle_existsUnique_middle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {x y : V} (hxy : x ≠ y)
    (hnotA : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y)
    (hnotB : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj x y)
    (u : a.supp) (v : b.supp)
    (hxu : G.Adj x u.1) (hyv : G.Adj y v.1) :
    ∃! z : V,
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x z ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj z y ∧
      G.Adj u.1 z ∧ G.Adj v.1 z := by
  obtain ⟨z, hz, huniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hab u v
  have hzx : z ≠ x := by
    intro h
    subst z
    apply hnotB
    exact componentOwnerGraph_adj_of_commonNeighbor_mem_owner
      G (secondOrderDefectGraph G) b hxy v.2 hz.2.symm hyv
  have hzy : z ≠ y := by
    intro h
    subst z
    apply hnotA
    exact componentOwnerGraph_adj_of_commonNeighbor_mem_owner
      G (secondOrderDefectGraph G) a hxy u.2 hxu hz.1.symm
  have hAz :
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x z :=
    componentOwnerGraph_adj_of_commonNeighbor_mem_owner
      G (secondOrderDefectGraph G) a hzx.symm u.2 hxu hz.1.symm
  have hBz :
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj z y :=
    componentOwnerGraph_adj_of_commonNeighbor_mem_owner
      G (secondOrderDefectGraph G) b hzy v.2 hz.2.symm hyv
  refine ⟨z, ⟨hAz, hBz, hz⟩, ?_⟩
  intro w hw
  exact huniq w ⟨hw.2.2.1, hw.2.2.2⟩

end

end Erdos85
