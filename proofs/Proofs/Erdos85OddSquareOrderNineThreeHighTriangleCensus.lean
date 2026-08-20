import Proofs.Erdos85OddSquareOrderNineThreeHighCoreOriginalEdgeConstraint

/-! # Triangle census at the three high roots of the q = 9 core

Node: B.3 / GAP B-CLASSIFY.  Every high root has degree ten and its induced
neighborhood is one-regular.  Hence it supports exactly five triangles.  In
the three-high branch the total rooted high-triangle contribution is exactly
fifteen, before the residual all-low triangles are counted.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A high root at square order `9^2` supports exactly five triangles. -/
theorem squareOrderNine_highRoot_localEdges_card_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {r : V}
    (hrH : r ∈ squareOrderHighVertices G 9) :
    (G.induce (G.neighborSet r)).edgeFinset.card = 5 := by
  let H := G.induce (G.neighborSet r)
  have hrDegree : G.degree r = 10 := (Finset.mem_filter.mp hrH).2
  have hlocal : ∀ s : {z : V // z ∈ G.neighborSet r}, H.degree s = 1 :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree (by norm_num) hmin hcard hrDegree).2.2
  have hvertices : Fintype.card {z : V // z ∈ G.neighborSet r} = 10 := by
    simpa [G.card_neighborFinset_eq_degree, hrDegree] using
      Fintype.card_coe (G.neighborFinset r)
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hsum : (∑ s : {z : V // z ∈ G.neighborSet r}, H.degree s) = 10 := by
    calc
      (∑ s : {z : V // z ∈ G.neighborSet r}, H.degree s) =
          ∑ _s : {z : V // z ∈ G.neighborSet r}, 1 := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact hlocal s
      _ = Fintype.card {z : V // z ∈ G.neighborSet r} := by simp
      _ = 10 := hvertices
  rw [hsum] at hhand
  change H.edgeFinset.card = 5
  omega

/-- Once the three high roots are named, their rooted triangle counts sum to
exactly fifteen.  High independence ensures this is also the unweighted
number of triangles containing a high vertex. -/
theorem squareOrderNine_threeHigh_localEdges_sum_eq_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9) :
    (G.induce (G.neighborSet a)).edgeFinset.card +
        (G.induce (G.neighborSet b)).edgeFinset.card +
        (G.induce (G.neighborSet c)).edgeFinset.card = 15 := by
  rw [squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard ha,
    squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard hb,
    squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard hc]

end

end Erdos85

#print axioms Erdos85.squareOrderNine_highRoot_localEdges_card_eq_five
#print axioms Erdos85.squareOrderNine_threeHigh_localEdges_sum_eq_fifteen
