import Proofs.Erdos85PlateauSlideNormalForm

/-!
# Packing the terminal edges of slide certificates

The penultimate vertex in a deleted-edge slide certificate determines the
donor neighbor uniquely.  Otherwise it and the donor center would have two
distinct common neighbors, producing a four-cycle.
-/

open SimpleGraph

namespace Erdos85

/-- For a fixed donor center `x`, surviving terminal edges `b-z` and `b-z'`
from the corresponding deleted-edge graphs force `z=z'`. -/
theorem deletedDonor_terminal_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x b z z' : V}
    (hxz : G.Adj x z) (hxz' : G.Adj x z')
    (hbz : (G.deleteEdges {s(x,z)}).Adj b z)
    (hbz' : (G.deleteEdges {s(x,z')}).Adj b z') :
    z = z' := by
  have hbzG : G.Adj b z := (SimpleGraph.deleteEdges_adj.mp hbz).1
  have hbzG' : G.Adj b z' := (SimpleGraph.deleteEdges_adj.mp hbz').1
  have hxb : x ≠ b := by
    intro h
    subst b
    exact (SimpleGraph.deleteEdges_adj.mp hbz).2 (by simp)
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz, hbzG⟩
  have hzmem' : z' ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz', hbzG'⟩
  exact Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree x b hxb) z hzmem z' hzmem'

/-- The terminal endpoint of a deleted-edge three-walk certificate is
injective as a function of its penultimate vertex, for fixed donor center. -/
theorem deletedThreeWalk_penultimate_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y z z' a a' b : V}
    (hxz : G.Adj x z) (hxz' : G.Adj x z')
    (hwalk : (G.deleteEdges {s(x,z)}).Adj y a ∧
      (G.deleteEdges {s(x,z)}).Adj a b ∧
      (G.deleteEdges {s(x,z)}).Adj b z)
    (hwalk' : (G.deleteEdges {s(x,z')}).Adj y a' ∧
      (G.deleteEdges {s(x,z')}).Adj a' b ∧
      (G.deleteEdges {s(x,z')}).Adj b z') :
    z = z' :=
  deletedDonor_terminal_unique G hfree hxz hxz' hwalk.2.2 hwalk'.2.2

end Erdos85
