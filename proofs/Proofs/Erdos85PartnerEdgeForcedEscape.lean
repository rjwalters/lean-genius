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

/-- Disjunctive form of `c4Free_partnerEdges_forces_target_escape`: one of
the two distinct cross-targets is genuinely outside the opposing edge. -/
theorem c4Free_partnerEdges_exists_target_escape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {a b c d p q : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (had : a ≠ d) (hbc : b ≠ c) (hac : a ≠ c) (hbd : b ≠ d)
    (hap : G.Adj a p) (hbq : G.Adj b q) (hpq : p ≠ q) :
    (p ≠ c ∧ p ≠ d) ∨ (q ≠ c ∧ q ≠ d) := by
  by_cases hp : p = c ∨ p = d
  · by_cases hq : q = c ∨ q = d
    · exact False.elim
        (c4Free_partnerEdges_forces_target_escape
          G hfree hab hcd had hbc hac hbd hap hbq hpq ⟨hp, hq⟩)
    · exact Or.inr (not_or.mp hq)
  · exact Or.inl (not_or.mp hp)

/-- Second-layer wrapper: for internal edges in two distinct root branches,
branch disjointness supplies all four endpoint inequalities automatically. -/
theorem c4Free_secondLayerPartnerEdges_exists_target_escape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s t : {z : V // z ∈ G.neighborSet v}} (hst : s ≠ t)
    {x₁ x₂ y₁ y₂ p q : V}
    (hx₁ : x₁ ∈ secondLayerBranch G v s)
    (hx₂ : x₂ ∈ secondLayerBranch G v s)
    (hy₁ : y₁ ∈ secondLayerBranch G v t)
    (hy₂ : y₂ ∈ secondLayerBranch G v t)
    (hxEdge : G.Adj x₁ x₂) (hyEdge : G.Adj y₁ y₂)
    (hxp : G.Adj x₁ p) (hxq : G.Adj x₂ q) (hpq : p ≠ q) :
    (p ≠ y₁ ∧ p ≠ y₂) ∨ (q ≠ y₁ ∧ q ≠ y₂) := by
  have hdisj : Disjoint (secondLayerBranch G v s)
      (secondLayerBranch G v t) :=
    secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hst
  have hne {x y : V} (hx : x ∈ secondLayerBranch G v s)
      (hy : y ∈ secondLayerBranch G v t) : x ≠ y := by
    intro hxy
    subst y
    exact Finset.disjoint_left.mp hdisj hx hy
  exact c4Free_partnerEdges_exists_target_escape
    G hfree hxEdge hyEdge
      (hne hx₁ hy₂) (hne hx₂ hy₁) (hne hx₁ hy₁) (hne hx₂ hy₂)
      hxp hxq hpq

end Erdos85

#print axioms Erdos85.c4Free_partnerEdges_forces_target_escape
#print axioms Erdos85.c4Free_partnerEdges_exists_target_escape
#print axioms Erdos85.c4Free_secondLayerPartnerEdges_exists_target_escape
