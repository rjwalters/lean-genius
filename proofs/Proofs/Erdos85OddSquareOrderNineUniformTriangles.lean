import Proofs.Erdos85OddPlaneOrderBipartiteObstruction
import Proofs.Erdos85GlobalLocalTriangleCount

/-!
# Uniform local triangle count at the odd square order q = 9

The plane-minus-two local window and the global three-to-one triangle count
interact sharply at order 80.  If every vertex has the same number of edges
in its induced neighborhood (in particular, in any vertex-transitive
candidate), that number is forced to be three.
-/

open SimpleGraph

namespace Erdos85

/-- A C4-free 9-regular graph on 80 vertices with uniform local triangle
count has exactly three edges in every induced neighborhood.

The local plane-order window gives `1 ≤ r ≤ 4`.  Globally, summing local
triangle edges counts each triangle three times, so `80*r` is divisible by
three.  Since `80` is coprime to three, the only value in the window is
`r = 3`. -/
theorem squareOrderNine_uniform_localTriangleEdge_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (r : ℕ)
    (huniform : ∀ v : V,
      (G.induce (G.neighborSet v)).edgeFinset.card = r) :
    r = 3 := by
  have hVpos : 0 < Fintype.card V := by omega
  let x : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
  have hbounds := planeMinusTwo_localTriangleEdge_card_bounds_of_odd
    G 9 (by norm_num) (by norm_num) (by omega) hregular hfree x
  rw [huniform x] at hbounds
  have hsum := sum_localTriangleEdges_eq_three_mul_triangularCliques G hfree
  simp_rw [huniform] at hsum
  simp [hcard] at hsum
  omega

end Erdos85
