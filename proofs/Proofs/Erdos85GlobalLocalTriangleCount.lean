import Proofs.Erdos85LocalTriangleParity

/-!
# Global count of local triangle edges

In a `C₄`-free graph, summing the number of edges in all neighborhood graphs
counts each triangle three times.  We prove this through the spanning graph of
edges lying in triangles; local linearity gives the global factor three.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Twice the number of edges in the neighborhood graph at `x` is the degree
of `x` in the spanning graph consisting of edges which lie in triangles. -/
theorem two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    2 * (G.induce (G.neighborSet x)).edgeFinset.card =
      (triangularEdgeGraph G).degree x := by
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges
    G hfree x
  have hsub : (triangleFreeNeighbors G x) ⊆ G.neighborFinset x := by
    intro y hy
    simpa [SimpleGraph.mem_neighborFinset] using
      ((mem_triangleFreeNeighbors G x y).mp hy).1
  have hneighbors : (triangularEdgeGraph G).neighborFinset x =
      G.neighborFinset x \ triangleFreeNeighbors G x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
    rw [triangularEdgeGraph_adj]
    constructor
    · rintro ⟨hxy, hcommon⟩
      exact ⟨hxy, fun htf => hcommon
        ((mem_triangleFreeNeighbors G x y).mp htf).2⟩
    · rintro ⟨hxy, hnot⟩
      refine ⟨hxy, ?_⟩
      intro hzero
      exact hnot ((mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hzero⟩)
  rw [← (triangularEdgeGraph G).card_neighborFinset_eq_degree,
    hneighbors, Finset.card_sdiff_of_subset hsub,
    G.card_neighborFinset_eq_degree]
  omega

/-- The sum of all rooted local-triangle edge counts is three times the
number of triangles in the triangular-edge graph.  Its cliques are precisely
the triangles of the original graph, but this form avoids needing that
identification downstream. -/
theorem sum_localTriangleEdges_eq_three_mul_triangularCliques
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    (∑ x : V, (G.induce (G.neighborSet x)).edgeFinset.card) =
      3 * ((triangularEdgeGraph G).cliqueFinset 3).card := by
  let T := triangularEdgeGraph G
  have hdegrees : 2 * (∑ x : V,
      (G.induce (G.neighborSet x)).edgeFinset.card) =
      ∑ x : V, T.degree x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree
      G hfree x
  have hhandshake : (∑ x : V, T.degree x) = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hlinear : T.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htriangles : T.edgeFinset.card =
      3 * (T.cliqueFinset 3).card := hlinear.card_edgeFinset
  rw [hhandshake, htriangles] at hdegrees
  change (∑ x : V, (G.induce (G.neighborSet x)).edgeFinset.card) =
    3 * (T.cliqueFinset 3).card
  omega

end

end Erdos85
