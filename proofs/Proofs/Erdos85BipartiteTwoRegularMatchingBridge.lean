import Proofs.Erdos85BipartiteShadowCycleType

/-! # From two-regular bipartite relations to matching shadows

This file packages the elementary bridge after one perfect matching has been
selected.  The residual edge at every vertex is another perfect matching, so
the two shore shadows fall under the q-generic conjugacy theorem.
-/

namespace Erdos85

/-- A relation with a unique partner on each shore canonically defines an
equivalence. -/
noncomputable def equivOfUniqueBipartiteRelation {S T : Type*}
    (R : S → T → Prop)
    (hS : ∀ s, ∃! t, R s t)
    (hT : ∀ t, ∃! s, R s t) : S ≃ T where
  toFun s := (hS s).choose
  invFun t := (hT t).choose
  left_inv s := by
    exact (hT ((hS s).choose)).unique
      (hT ((hS s).choose)).choose_spec.1 (hS s).choose_spec.1
  right_inv t := by
    exact (hS ((hT t).choose)).unique
      (hS ((hT t).choose)).choose_spec.1 (hT t).choose_spec.1

theorem equivOfUniqueBipartiteRelation_apply_rel {S T : Type*}
    (R : S → T → Prop)
    (hS : ∀ s, ∃! t, R s t)
    (hT : ∀ t, ∃! s, R s t) (s : S) :
    R s (equivOfUniqueBipartiteRelation R hS hT s) :=
  (hS s).choose_spec.1

/-- The residual relation after deleting a displayed perfect matching. -/
def residualBipartiteRelation {S T : Type*} (R : S → T → Prop)
    (f : S ≃ T) : S → T → Prop :=
  fun s t => R s t ∧ t ≠ f s

/-- Exact data needed from a two-regular bipartite block after selecting one
perfect matching.  Degree two makes both uniqueness clauses automatic; they
are exposed here so the later graph adapter has a small target. -/
structure BipartiteTwoRegularAfterMatching {S T : Type*}
    (R : S → T → Prop) (f : S ≃ T) : Prop where
  matching_mem : ∀ s, R s (f s)
  residual_unique_left : ∀ s, ∃! t, residualBipartiteRelation R f s t
  residual_unique_right : ∀ t, ∃! s, residualBipartiteRelation R f s t

noncomputable def BipartiteTwoRegularAfterMatching.residualEquiv
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) : S ≃ T :=
  equivOfUniqueBipartiteRelation (residualBipartiteRelation R f)
    h.residual_unique_left h.residual_unique_right

theorem BipartiteTwoRegularAfterMatching.residualEquiv_mem
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) (s : S) :
    R s (h.residualEquiv s) ∧ h.residualEquiv s ≠ f s :=
  equivOfUniqueBipartiteRelation_apply_rel
    (residualBipartiteRelation R f)
    h.residual_unique_left h.residual_unique_right s

theorem BipartiteTwoRegularAfterMatching.matchings_disjoint
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) (s : S) :
    h.residualEquiv s ≠ f s :=
  (h.residualEquiv_mem s).2

/-- The two shore shadows of a two-regular bipartite relation have identical
cycle profiles once one perfect matching is selected. -/
theorem BipartiteTwoRegularAfterMatching.shadow_cycleProfile_eq
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) :
    permutationCycleProfile S
        (bipartiteLeftShadow f h.residualEquiv) =
      permutationCycleProfile T
        (bipartiteRightShadow f h.residualEquiv) :=
  bipartiteShadows_cycleProfile_eq f h.residualEquiv

/-- Neither shore shadow has a fixed point when the two matchings are
edge-disjoint. -/
theorem BipartiteTwoRegularAfterMatching.leftShadow_no_fixedPoint
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) (s : S) :
    bipartiteLeftShadow f h.residualEquiv s ≠ s := by
  rw [Ne, bipartiteLeftShadow_apply_eq_iff]
  exact h.matchings_disjoint s

end Erdos85
