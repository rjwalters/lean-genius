import Proofs.Erdos85GadgetDegreeSquares

/-!
# A C4-free graph on sixteen vertices has at most 35 edges

This small numerical consequence of the standard cherry bound is used for
the sixteen `H`-cells in the mixed `mu = 3` grid.  It is deliberately proved
without enumeration: Cauchy--Schwarz and the common-neighbour cherry count
give a quadratic inequality for the total degree.
-/

open SimpleGraph

namespace Erdos85

/-- A C4-free simple graph on sixteen vertices has at most 35 edges. -/
theorem card_edges_le_thirtyFive_of_card_sixteen_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hfree : ¬ containsC4 V G) :
    G.edgeFinset.card ≤ 35 := by
  have hcherry :=
    sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hcauchy := sum_degrees_sq_le_card_mul_sum_degree_sq G
  have hid : (∑ v : V, G.degree v * G.degree v) =
      2 * (∑ v : V, (G.degree v).choose 2) + ∑ v : V, G.degree v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact (two_mul_choose_two_add_self (G.degree v)).symm
  have hhand := G.sum_degrees_eq_twice_card_edges
  rw [hcard] at hcherry hcauchy
  norm_num [Nat.choose] at hcherry
  rw [hid, hhand] at hcauchy
  nlinarith

end Erdos85

#print axioms Erdos85.card_edges_le_thirtyFive_of_card_sixteen_of_not_containsC4
