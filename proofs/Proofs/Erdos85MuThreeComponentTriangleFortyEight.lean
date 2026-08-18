import Proofs.Erdos85LocalTriangleParity

/-!
# The 48 rooted triangles of a mu=3 size-two component

At degree eight, a vertex with exactly two triangle-free incident edges has
three edges in its induced neighbourhood, hence three rooted triangles.  A
sixteen-vertex component all of whose vertices have triangle-free degree two
therefore contributes exactly 48 rooted local triangles.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Degree eight and triangle-free degree two force exactly three local
triangle edges at one vertex. -/
theorem localTriangleEdges_eq_three_of_degree_eight_of_triangleFree_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (hdegree : G.degree x = 8)
    (htf : (triangleFreeNeighbors G x).card = 2) :
    (G.induce (G.neighborSet x)).edgeFinset.card = 3 := by
  have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  rw [hdegree, htf] at hid
  omega

/-- **The 48 count.**  Sixteen vertices, each rooting three local triangles,
give exactly 48 rooted incidences. -/
theorem sum_localTriangleEdges_eq_fortyEight_of_card_sixteen_degree_eight_tf_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S : Set V) [DecidablePred (· ∈ S)]
    (hcard : Fintype.card S = 16)
    (hdegree : ∀ x : S, G.degree x.1 = 8)
    (htf : ∀ x : S, (triangleFreeNeighbors G x.1).card = 2) :
    (∑ x : S, (G.induce (G.neighborSet x.1)).edgeFinset.card) = 48 := by
  calc
    (∑ x : S, (G.induce (G.neighborSet x.1)).edgeFinset.card) =
        ∑ _x : S, 3 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact localTriangleEdges_eq_three_of_degree_eight_of_triangleFree_card_eq_two
        G hfree x.1 (hdegree x) (htf x)
    _ = 48 := by simp [hcard]

end

end Erdos85

#print axioms
  Erdos85.localTriangleEdges_eq_three_of_degree_eight_of_triangleFree_card_eq_two
#print axioms
  Erdos85.sum_localTriangleEdges_eq_fortyEight_of_card_sixteen_degree_eight_tf_two
