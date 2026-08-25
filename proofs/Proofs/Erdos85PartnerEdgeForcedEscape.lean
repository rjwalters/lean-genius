import Proofs.Erdos85ExteriorPermutationCodeRectangle

/-!
# A partner edge forces a cross-target escape

If the endpoints of one edge have distinct targets among the endpoints of a
second edge, the two target edges complete either the parallel or the crossed
rectangle.  A `C₄`-free graph therefore forces at least one target outside the
second edge.  This is the abstract step used by the odd-profile four-pair
transversal argument.
-/

namespace Erdos85

open SimpleGraph

/-- Distinct cross-targets of one edge cannot both be the endpoints of a
second edge in a `C₄`-free graph. -/
theorem c4Free_partnerEdges_forces_target_escape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {a b c d p q : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (had : a ≠ d) (hbc : b ≠ c) (hac : a ≠ c) (hbd : b ≠ d)
    (hap : G.Adj a p) (hbq : G.Adj b q) (hpq : p ≠ q) :
    ¬ ((p = c ∨ p = d) ∧ (q = c ∨ q = d)) := by
  rintro ⟨hp, hq⟩
  obtain ⟨hparallel, hcrossed⟩ :=
    c4Free_partnerEdges_rectangle_dichotomy
      G hfree hab hcd had hbc hac hbd
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact hpq rfl
  · exact hparallel ⟨hap, hbq⟩
  · exact hcrossed ⟨hap, hbq⟩
  · exact hpq rfl

end Erdos85

#print axioms Erdos85.c4Free_partnerEdges_forces_target_escape
