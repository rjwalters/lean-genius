import Proofs.Erdos85StarActivityTriangleEdgeCut

/-!
# Graph realization of the triangle-edge activity cut

The selected non-`T` star crossings counted by the activity identity are
literally the selected neighbors in the binary support cut of `A \ T`.
This gives the exact located-graph form of `(73rnz_cjibkzh)`.
-/

open SimpleGraph

namespace Erdos85

/-- The local activity-cut finset is exactly the selected neighborhood in
the support cut of the non-`T` part of `A`. -/
theorem starTriangleEdgeCutNeighbors_eq_cutGraph_neighborFinset_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (X : Finset V) (t : V → ZMod 2) (y : V) :
    starTriangleEdgeCutNeighbors A T X t y =
      (binaryVertexCutGraph (A \ T) (f2PotentialSupport t)).neighborFinset y ∩ X := by
  ext u
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary (t u) with hu | hu <;>
    rcases hbinary (t y) with hy | hy <;>
    simp [starTriangleEdgeCutNeighbors, binaryVertexCutGraph,
      f2PotentialSupport, SimpleGraph.mem_neighborFinset, sdiff_adj, hu, hy] <;>
    aesop

/-- Consequently the local activity is the F₂ degree, restricted to `X`,
of the literal `(A \ T)` support-cut graph. -/
theorem sum_f2_neighbor_inter_eq_triangleEdgeCutGraph_neighbor_inter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (X : Finset V) (t : V → ZMod 2) (y : V)
    (heven : Even (A.neighborFinset y ∩ X).card)
    (hTconst : ∀ u, u ∈ A.neighborFinset y ∩ X →
      T.Adj y u → t u = t y) :
    (∑ u ∈ A.neighborFinset y ∩ X, t u) =
      (((binaryVertexCutGraph (A \ T)
        (f2PotentialSupport t)).neighborFinset y ∩ X).card : ZMod 2) := by
  rw [← starTriangleEdgeCutNeighbors_eq_cutGraph_neighborFinset_inter]
  exact sum_f2_neighbor_inter_eq_starTriangleEdgeCutNeighbors_card
    A T X t y heven hTconst

end Erdos85

#print axioms Erdos85.starTriangleEdgeCutNeighbors_eq_cutGraph_neighborFinset_inter
#print axioms Erdos85.sum_f2_neighbor_inter_eq_triangleEdgeCutGraph_neighbor_inter_card
