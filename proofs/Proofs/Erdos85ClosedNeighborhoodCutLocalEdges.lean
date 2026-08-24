import Proofs.Erdos85ClosedNeighborhoodCutTriangleIdentity
import Proofs.Erdos85DistanceLayers

/-!
# Closed-neighborhood cuts and local edge counts

This converts the ordered common-neighbor sum in the closed-star cut
identity into twice the edge count of the induced neighborhood graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordered common-neighbor count rooted at `x` is twice the number of
edges in the graph induced by `N(x)`. -/
theorem sum_neighbor_common_card_eq_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (x : V) :
    (∑ u ∈ D.neighborFinset x,
        (D.neighborFinset u ∩ D.neighborFinset x).card) =
      2 * (D.induce (D.neighborSet x)).edgeFinset.card := by
  classical
  have hhand :=
    SimpleGraph.sum_degrees_eq_twice_card_edges
      (D.induce (D.neighborSet x))
  calc
    (∑ u ∈ D.neighborFinset x,
        (D.neighborFinset u ∩ D.neighborFinset x).card) =
        ∑ u : {z : V // z ∈ D.neighborSet x},
          (D.induce (D.neighborSet x)).degree u := by
            rw [Finset.sum_subtype (D.neighborFinset x)
              (fun u ↦ D.mem_neighborFinset x u)]
            apply Finset.sum_congr rfl
            intro u _
            rw [degree_induce_neighborSet_eq_card_common]
            rw [Finset.inter_comm]
    _ = _ := hhand

/-- Exact local-triangle form of the closed-neighborhood cut identity. -/
theorem closedNeighborhood_cut_add_two_mul_degree_add_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ x, D.degree x = r) (x : V) :
    finsetGraphCutSize D (insert x (D.neighborFinset x)) +
        (2 * r + 2 * (D.induce (D.neighborSet x)).edgeFinset.card) =
      (r + 1) * r := by
  rw [← sum_neighbor_common_card_eq_two_mul_localEdges D x]
  exact closedNeighborhood_cut_add_two_mul_degree_add_common_sum D hreg x

end

end Erdos85

#print axioms Erdos85.sum_neighbor_common_card_eq_two_mul_localEdges
#print axioms Erdos85.closedNeighborhood_cut_add_two_mul_degree_add_two_mul_localEdges
