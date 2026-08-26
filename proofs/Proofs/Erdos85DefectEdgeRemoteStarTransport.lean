import Proofs.Erdos85TriangleFreeNeighborhoodCut
import Proofs.Erdos85ClosedNeighborhoodCutLocalEdges
import Proofs.Erdos85LocalTriangleParity

/-!
# Open-neighborhood cut transport along a defect edge

For a regular graph, the cut leaving an open neighborhood records exactly
the local triangle deficit.  In a C4-free graph this deficit is the degree in
the triangle-free-edge graph.  Consequently propagation of that degree along
an edge of the second-order defect graph is equivalent to equality of the two
ambient open-neighborhood cuts.

This is the exact cut-level transport equation behind the remote-star route:
after the common cross-star contribution is removed, the difference of the
two remote contact masses is the difference of the triangle-free degrees.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- In an `r`-regular graph, the cut leaving `N(x)`, plus twice the number of
edges internal to `N(x)`, is `r²`. -/
theorem regular_neighborFinset_cut_add_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hreg : ∀ y, G.degree y = r) (x : V) :
    finsetGraphCutSize G (G.neighborFinset x) +
        2 * (G.induce (G.neighborSet x)).edgeFinset.card = r * r := by
  rw [← sum_neighbor_common_card_eq_two_mul_localEdges G x]
  rw [finsetGraphCutSize, ← Finset.sum_add_distrib]
  calc
    (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y \ G.neighborFinset x).card +
          (G.neighborFinset y ∩ G.neighborFinset x).card)) =
        ∑ y ∈ G.neighborFinset x, G.degree y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← G.card_neighborFinset_eq_degree]
      have hpartition := Finset.card_inter_add_card_sdiff
        (G.neighborFinset y) (G.neighborFinset x)
      omega
    _ = r * r := by simp [hreg, G.card_neighborFinset_eq_degree]

/-- In a regular C4-free graph the ambient cut of `N(x)` transports the
triangle-free-edge degree at `x`, without subtraction in `ℕ`. -/
theorem regular_c4Free_neighborFinset_cut_add_degree_eq_square_add_triangleFreeDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ y, G.degree y = q) (x : V) :
    finsetGraphCutSize G (G.neighborFinset x) + q =
      q * q + (triangleFreeEdgeGraph G).degree x := by
  have hcut := regular_neighborFinset_cut_add_two_mul_localEdges G hreg x
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have hk : (triangleFreeEdgeGraph G).degree x =
      (triangleFreeNeighbors G x).card := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
  rw [hreg x] at hlocal
  omega

/-- Along any pair of vertices (in particular a defect edge), equality of
triangle-free degrees is exactly equality of the two ambient neighborhood
cuts.  The defect adjacency hypothesis records the intended transport lane. -/
theorem secondOrderDefect_adj_triangleFreeDegree_eq_iff_neighborFinset_cut_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ y, G.degree y = q) {u v : V}
    (_huv : (secondOrderDefectGraph G).Adj u v) :
    (triangleFreeEdgeGraph G).degree u =
        (triangleFreeEdgeGraph G).degree v ↔
      finsetGraphCutSize G (G.neighborFinset u) =
        finsetGraphCutSize G (G.neighborFinset v) := by
  have hu :=
    regular_c4Free_neighborFinset_cut_add_degree_eq_square_add_triangleFreeDegree
      G hfree hreg u
  have hv :=
    regular_c4Free_neighborFinset_cut_add_degree_eq_square_add_triangleFreeDegree
      G hfree hreg v
  omega

end

end Erdos85

#print axioms Erdos85.regular_neighborFinset_cut_add_two_mul_localEdges
#print axioms
  Erdos85.regular_c4Free_neighborFinset_cut_add_degree_eq_square_add_triangleFreeDegree
#print axioms
  Erdos85.secondOrderDefect_adj_triangleFreeDegree_eq_iff_neighborFinset_cut_eq
