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

/-- In the degree-thirteen, order-192 Stage-1 residual, 328 triangles leave
exactly 264 edges which lie in no triangle.  These are precisely the
`H ∩ A` edges in the zero-layer square identity. -/
theorem degree_thirteen_order_192_triangleFreeEdgeGraph_card_eq_264
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 192)
    (hreg : ∀ x : V, G.degree x = 13)
    (htriangles : ((triangularEdgeGraph G).cliqueFinset 3).card = 328) :
    (triangleFreeEdgeGraph G).edgeFinset.card = 264 := by
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hedgeG : G.edgeFinset.card = 1248 := by
    have hhandshake := G.sum_degrees_eq_twice_card_edges
    simp_rw [hreg] at hhandshake
    simp [hcard] at hhandshake
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have hedgeH : H.edgeFinset.card = 984 := by
    rw [hlocal.card_edgeFinset, htriangles]
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    have hle := Finset.card_le_card (edgeFinset_mono hTle)
    omega
  rw [hedgeG, hedgeH] at hpartition
  change T.edgeFinset.card = 264
  omega

/-- A mixed third trace counts, with orientation, the common `A`-neighbors
across the edges of `H`.  This is the graph bridge for the fixed Stage-1
identity `tr(H A²) = 15696`. -/
theorem trace_adjMatrix_mul_adjMatrix_sq_eq_sum_common_over_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H A : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel A.Adj] :
    Matrix.trace (H.adjMatrix ℤ * (A.adjMatrix ℤ * A.adjMatrix ℤ)) =
      ∑ x : V, ∑ y ∈ H.neighborFinset x,
        ((A.neighborFinset x ∩ A.neighborFinset y).card : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp only [adjMatrix_sq_apply_eq_card_common,
    SimpleGraph.adjMatrix_apply]
  classical
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext y
    simp [SimpleGraph.mem_neighborFinset]
  · intro y hy
    simp [Finset.inter_comm]

/-- If the 192 local overlap degrees are odd and have total 528 (twice the
264 overlap edges), their total half-excess above one is exactly 168. -/
theorem sum_half_excess_eq_168_of_odd_overlap_degrees
    {V : Type*} [Fintype V]
    (overlapDegree halfExcess : V → ℕ)
    (hcard : Fintype.card V = 192)
    (hodd : ∀ x, overlapDegree x = 2 * halfExcess x + 1)
    (hsum : (∑ x : V, overlapDegree x) = 528) :
    (∑ x : V, halfExcess x) = 168 := by
  simp_rw [hodd] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp [hcard] at hsum
  omega

end

end Erdos85
