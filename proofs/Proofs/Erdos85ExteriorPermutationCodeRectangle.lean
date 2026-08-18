import Proofs.Erdos85ExteriorRowPartnerDichotomy

/-! # The local rectangle clauses of the exterior permutation code

For two disjoint partner edges, C4-freeness forbids both possible two-edge
completions of their rectangle.  These are exactly the C3 clauses saying that
an inter-row map cannot fix both members of a common partner pair and cannot
swap that pair.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two disjoint partner edges cannot be joined in parallel: that would be a
four-cycle. -/
theorem c4Free_partnerEdges_not_parallel_complete
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (had : a ≠ d) (hbc : b ≠ c) :
    ¬ (G.Adj a c ∧ G.Adj b d) := by
  rintro ⟨hac, hbd⟩
  have h := c4Free_commonNeighborPair_injective G hfree had
    hab hac hbd.symm hcd.symm
  exact hbc h

/-- Two disjoint partner edges cannot be joined crosswise: that would be the
other four-cycle completion of the same rectangle. -/
theorem c4Free_partnerEdges_not_cross_complete
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (G.Adj a d ∧ G.Adj b c) := by
  rintro ⟨had, hbc⟩
  have h := c4Free_commonNeighborPair_injective G hfree hac
    hab had hbc.symm hcd
  exact hbd h

/-- Combined C3 rectangle package: neither the parallel nor the crossed
completion is possible. -/
theorem c4Free_partnerEdges_rectangle_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (had : a ≠ d) (hbc : b ≠ c) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (G.Adj a c ∧ G.Adj b d) ∧ ¬ (G.Adj a d ∧ G.Adj b c) :=
  ⟨c4Free_partnerEdges_not_parallel_complete G hfree hab hcd had hbc,
    c4Free_partnerEdges_not_cross_complete G hfree hab hcd hac hbd⟩

end


end Erdos85

#print axioms Erdos85.c4Free_partnerEdges_rectangle_dichotomy
