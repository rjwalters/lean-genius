import Proofs.Erdos85OrderFortyNineOneThreeHighProfile

/-!
# High-support partitions around low vertices

The exact common-neighbor law says more than a weighted identity: the high
supports carried by the graph neighbors of any low vertex are pairwise
disjoint and cover the high sector.  This is the structural interface used
both in hand arguments and in the finite certificate reduction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The high supports of the graph neighbors of a low vertex cover every
high point. -/
theorem orderFortyNine_graphNeighbor_highSupports_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y w : V}
    (hy : G.degree y = 7) :
    w ∈ orderFortyNineHighVertices G ↔
      ∃ x ∈ G.neighborFinset y, w ∈ orderFortyNineHighSupport G x := by
  constructor
  · intro hw
    rcases orderFortyNine_low_neighborhood_partitions_highs
        G hfree hmin hcard hy hw with ⟨x, hx, _huniq⟩
    refine ⟨x, hx.1, ?_⟩
    apply Finset.mem_inter.mpr
    exact ⟨by simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hx.2, hw⟩
  · rintro ⟨x, _hxy, hw⟩
    exact (Finset.mem_inter.mp hw).2

/-- Distinct graph neighbors of a low vertex carry disjoint high supports. -/
theorem orderFortyNine_graphNeighbor_highSupports_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y x z : V}
    (hy : G.degree y = 7)
    (hxy : x ∈ G.neighborFinset y) (hzy : z ∈ G.neighborFinset y)
    (hxz : x ≠ z) :
    Disjoint (orderFortyNineHighSupport G x)
      (orderFortyNineHighSupport G z) := by
  rw [Finset.disjoint_left]
  intro w hwx hwz
  have hwH : w ∈ orderFortyNineHighVertices G :=
    (Finset.mem_inter.mp hwx).2
  rcases orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin hcard hy hwH with ⟨u, hu, huniq⟩
  have hxProp : x ∈ G.neighborFinset y ∧ G.Adj x w := by
    refine ⟨hxy, ?_⟩
    have := (Finset.mem_inter.mp hwx).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hzProp : z ∈ G.neighborFinset y ∧ G.Adj z w := by
    refine ⟨hzy, ?_⟩
    have := (Finset.mem_inter.mp hwz).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  exact hxz ((huniq x hxProp).trans (huniq z hzProp).symm)

/-- The two preceding theorems package the graph-neighbor high supports as
an exact set partition: every high belongs to one and only one neighbor
support. -/
theorem orderFortyNine_existsUnique_graphNeighbor_carrying_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y w : V}
    (hy : G.degree y = 7)
    (hw : w ∈ orderFortyNineHighVertices G) :
    ∃! x, x ∈ G.neighborFinset y ∧
      w ∈ orderFortyNineHighSupport G x := by
  rcases orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin hcard hy hw with ⟨x, hx, huniq⟩
  refine ⟨x, ⟨hx.1, ?_⟩, ?_⟩
  · exact Finset.mem_inter.mpr
      ⟨by simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hx.2, hw⟩
  · intro z hz
    apply huniq z
    refine ⟨hz.1, ?_⟩
    have := (Finset.mem_inter.mp hz.2).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this

end

end Erdos85
