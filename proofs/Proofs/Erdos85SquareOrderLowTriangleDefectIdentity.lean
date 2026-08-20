import Proofs.Erdos85SquareOrderDefectIncidence
import Proofs.Erdos85LocalTriangleParity

/-! # Triangle-corrected two-ball identity at square order

For a low vertex at exact order `d²`, the defect-degree ledger and the local
triangle handshake combine to identify the antipodal misses exactly.  This
explains why the coarser defect-incidence equation contains no explicit
triangle term: triangle-free defect edges and local triangle edges cancel.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At a degree-`d` vertex of an exact square-order tight-cover graph, twice
the number of edges in its open neighborhood equals the number of antipodal
misses plus its high-neighbor incidence plus one. -/
theorem squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V}
    (hx : G.degree x = d) :
    (antipodalNeighbors G x).card +
        squareOrderHighIncidenceCount G d x + 1 =
      2 * (G.induce (G.neighborSet x)).edgeFinset.card := by
  have hdefect := squareOrder_defectDegree_add_highIncidence_eq_pred
    G hfree hd hmin hcover hcard hx
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset G x,
    Finset.card_union_of_disjoint
      (disjoint_antipodal_triangleFreeNeighbors G x)] at hdefect
  have htriangle := card_triangleFreeNeighbors_add_two_mul_localEdges
    G hfree x
  rw [hx] at htriangle
  omega

end

end Erdos85

#print axioms Erdos85.squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
