import Proofs.Erdos85ConnectedIncidenceBottleneckCutEnergy

/-!
# Triangle-free degree mass as a neighborhood cut

For the graph `K` of ambient edges lying in no triangle, every ambient open
neighborhood is independent in `K`.  Consequently the `K`-degree mass seen
by ambient adjacency is exactly the `K`-cut of that neighborhood.  This is
the graph-facing form of the weighted-neighbor target in the connected
binary-square terminal.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- A triangle-free-edge neighborhood of a vertex in `N_G(x)` is disjoint
from `N_G(x)`: otherwise `x` would be a common neighbor of that edge. -/
theorem triangleFreeEdgeGraph_neighbor_disjoint_ambient_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x : V) {y : V} (hy : y ∈ G.neighborFinset x) :
    Disjoint ((triangleFreeEdgeGraph G).neighborFinset y)
      (G.neighborFinset x) := by
  rw [Finset.disjoint_left]
  intro z hzK hzG
  have hyAdj : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  have hzAdj : G.Adj x z := (G.mem_neighborFinset x z).mp hzG
  have htf := (mem_triangleFreeNeighbors G y z).mp
    ((triangleFreeEdgeGraph G).mem_neighborFinset y z |>.mp hzK)
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset z := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hyAdj.symm, hzAdj.symm⟩
  have hpos : 0 < (G.neighborFinset y ∩ G.neighborFinset z).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  rw [htf.2] at hpos
  omega

/-- The triangle-free-degree mass across an ambient neighborhood equals the
cut of that neighborhood in the triangle-free-edge graph. -/
theorem adjMatrix_mulVec_triangleFreeDegree_eq_neighborFinset_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x : V) :
    (G.adjMatrix ℕ).mulVec
        (fun y => (triangleFreeEdgeGraph G).degree y) x =
      finsetGraphCutIncidenceCount (triangleFreeEdgeGraph G)
        (G.neighborFinset x) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  unfold finsetGraphCutIncidenceCount
  apply Finset.sum_congr rfl
  intro y hy
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
  have hdisj :=
    triangleFreeEdgeGraph_neighbor_disjoint_ambient_neighborFinset G x hy
  have heq : (triangleFreeEdgeGraph G).neighborFinset y \
      G.neighborFinset x = (triangleFreeEdgeGraph G).neighborFinset y := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      exact (Finset.mem_sdiff.mp hz).1
    · intro hz
      exact Finset.mem_sdiff.mpr
        ⟨hz, fun hzN => Finset.disjoint_left.mp hdisj hz hzN⟩
  rw [heq]

/-- Rational form used directly by the weighted-neighbor kernel terminal. -/
theorem adjMatrix_mulVec_triangleFreeDegree_rat_eq_neighborFinset_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x : V) :
    (G.adjMatrix ℚ).mulVec
        (fun y => ((triangleFreeEdgeGraph G).degree y : ℚ)) x =
      (finsetGraphCutIncidenceCount (triangleFreeEdgeGraph G)
        (G.neighborFinset x) : ℚ) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hnat := adjMatrix_mulVec_triangleFreeDegree_eq_neighborFinset_cut G x
  rw [SimpleGraph.adjMatrix_mulVec_apply] at hnat
  exact_mod_cast hnat

/-- The weighted-neighbor identity is exactly uniformity of the
triangle-free-edge cut across all ambient open neighborhoods. -/
theorem triangleFreeDegree_weightedNeighbor_iff_neighborFinset_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : ℚ) :
    ((G.adjMatrix ℚ).mulVec
        (fun y => ((triangleFreeEdgeGraph G).degree y : ℚ)) =
      fun _ => c) ↔
      ∀ x, (finsetGraphCutIncidenceCount (triangleFreeEdgeGraph G)
        (G.neighborFinset x) : ℚ) = c := by
  constructor
  · intro h x
    rw [← adjMatrix_mulVec_triangleFreeDegree_rat_eq_neighborFinset_cut G x]
    exact congrFun h x
  · intro h
    funext x
    rw [adjMatrix_mulVec_triangleFreeDegree_rat_eq_neighborFinset_cut G x]
    exact h x

end

end Erdos85

#print axioms Erdos85.triangleFreeEdgeGraph_neighbor_disjoint_ambient_neighborFinset
#print axioms Erdos85.adjMatrix_mulVec_triangleFreeDegree_eq_neighborFinset_cut
#print axioms Erdos85.adjMatrix_mulVec_triangleFreeDegree_rat_eq_neighborFinset_cut
#print axioms Erdos85.triangleFreeDegree_weightedNeighbor_iff_neighborFinset_cut
