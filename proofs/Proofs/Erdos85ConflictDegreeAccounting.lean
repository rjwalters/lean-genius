import Proofs.Erdos85ConflictRegular

/-!
# Exact conflict-degree accounting

The common-neighbour conflict degree is the sum of the degree deficits along
the first step of every two-step walk.  This holds without regularity.  Under
the tight-edge-cover condition of an edge-minimal witness, every neighbour of
a non-tight vertex is tight, so the formula specializes exactly to
`degree x * (d - 1)`.
-/

open SimpleGraph Finset

namespace Erdos85

/-- **Exact nonregular conflict degree.**  In a `C₄`-free graph, the
two-step branches out of `x` are disjoint, and the branch through `y` has
`degree y - 1` vertices. -/
theorem degree_commonNeighborConflict_eq_sum_neighbor_degree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (commonNeighborConflict G).degree x =
      ∑ y : {z : V // z ∈ G.neighborSet x}, (G.degree y.1 - 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_commonNeighborConflict_eq_biUnion_conflictBranch,
    Finset.card_biUnion (conflictBranch_pairwiseDisjoint G hfree x)]
  apply Finset.sum_congr rfl
  intro y _
  rw [conflictBranch, Finset.card_erase_of_mem,
    G.card_neighborFinset_eq_degree]
  exact (G.mem_neighborFinset y.1 x).mpr y.2.symm

/-- In an edge-minimal minimum-degree-`d` graph, the conflict degree of every
non-tight vertex is known exactly: all of its neighbours are tight. -/
theorem degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (x : V) (hx : G.degree x ≠ d) :
    (commonNeighborConflict G).degree x = G.degree x * (d - 1) := by
  rw [degree_commonNeighborConflict_eq_sum_neighbor_degree_sub_one G hfree x]
  have hneighbor : ∀ y : {z : V // z ∈ G.neighborSet x},
      G.degree y.1 = d := by
    intro y
    rcases hcover y.2 with hxtight | hytight
    · exact (hx hxtight).elim
    · exact hytight
  calc
    (∑ y : {z : V // z ∈ G.neighborSet x}, (G.degree y.1 - 1)) =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, (d - 1) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hneighbor y]
    _ = G.degree x * (d - 1) := by
      rw [Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_neighborSet_eq_degree]
      simp

/-- Tight vertices and non-tight vertices form an edge cover partition: two
non-tight vertices can never be adjacent. -/
theorem not_adj_of_degree_ne_of_degree_ne_of_tight_edge_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    {u v : V} (hu : G.degree u ≠ d) (hv : G.degree v ≠ d) :
    ¬ G.Adj u v := by
  intro huv
  rcases hcover huv with hutight | hvtight
  · exact hu hutight
  · exact hv hvtight

end Erdos85
