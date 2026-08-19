import Proofs.Erdos85SixTenMixedOwnerCertificate
import Proofs.Erdos85EightEightLowOwnerCnfSemantics

/-!
# Semantic socket for the mixed six-plus-ten owner CNF

The four fields expose exactly the service and C4 consequences needed by
the generated clause families.  All finite bookkeeping and the checked
LRAT contradiction are discharged below.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

set_option maxHeartbeats 0

structure SixTenMixedOwnerConstraintSemantics
    (val : DimacsValuation) : Prop where
  service_exists : ∀ e v,
    e < 48 → v < 16 → sixTenMixedOwnerTargetContains e v = true →
      dimacsClauseSatisfied val (sixTenMixedOwnerServiceVariables e v)
  service_unique : ∀ e v clause,
    e < 48 → v < 16 → sixTenMixedOwnerTargetContains e v = true →
      clause ∈ eightEightPairwiseNegativeClauses
        (sixTenMixedOwnerServiceVariables e v) →
      dimacsClauseSatisfied val clause
  intersecting_no_common : ∀ e f clause,
    e < f → f < 48 → sixTenMixedOwnersIntersect e f = true →
      clause ∈ sixTenMixedOwnerNoCommonClauses e f →
      dimacsClauseSatisfied val clause
  no_two_common : ∀ e f clause,
    e < f → f < 48 → sixTenMixedOwnersIntersect e f = false →
      clause ∈ sixTenMixedOwnerAtMostOneCommonClauses e f →
      dimacsClauseSatisfied val clause

theorem sixTenMixedOwnerConstraintSemantics_formulaSatisfied
    {val : DimacsValuation}
    (h : SixTenMixedOwnerConstraintSemantics val) :
    dimacsFormulaSatisfied val sixTenMixedOwnerDimacsClauses := by
  intro clause hclause
  simp only [sixTenMixedOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hservice | hc4
  · simp only [sixTenMixedOwnerServiceClauses, List.mem_flatMap,
      List.mem_range] at hservice
    obtain ⟨e, he48, v, hv16, hclause⟩ := hservice
    split at hclause
    · next htarget =>
      rcases List.mem_append.mp hclause with hexists | hunique
      · simp only [List.mem_singleton] at hexists
        subst clause
        exact h.service_exists e v he48 hv16 (by
          simpa only [sixTenMixedOwnerTargetContains] using htarget)
      · exact h.service_unique e v clause he48 hv16 (by
          simpa only [sixTenMixedOwnerTargetContains] using htarget)
          hunique
    · simp at hclause
  · simp only [sixTenMixedOwnerC4Clauses, List.mem_flatMap,
      List.mem_range, List.mem_filter] at hc4
    obtain ⟨e, he48, f, ⟨hf48, hef⟩, hclause⟩ := hc4
    split at hclause
    · next hintersect =>
      exact h.intersecting_no_common e f clause (of_decide_eq_true hef) hf48
        (by simpa using hintersect) hclause
    · next hdisjoint =>
      exact h.no_two_common e f clause (of_decide_eq_true hef) hf48
        (by simpa using hdisjoint) hclause

set_option maxHeartbeats 0 in
theorem sixTenMixedOwnerDimacsClauses_all_ne_zero :
    ∀ i : Fin sixTenMixedOwnerDimacsClauses.size,
      (sixTenMixedOwnerDimacsClauses[i].all fun lit => lit != 0) = true := by
  native_decide

theorem sixTenMixedOwnerDimacsClauses_nonzero
    (i : Fin sixTenMixedOwnerDimacsClauses.size) :
    DimacsClauseNonzero sixTenMixedOwnerDimacsClauses[i] := by
  intro lit hlit
  have hne := List.all_eq_true.mp
    (sixTenMixedOwnerDimacsClauses_all_ne_zero i) lit hlit
  simpa using hne

theorem sixTenMixedOwnerDimacsClauses_nonzero_of_mem :
    ∀ clause ∈ sixTenMixedOwnerDimacsClauses,
      DimacsClauseNonzero clause := by
  intro clause hclause
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hclause
  rw [← heq]
  exact sixTenMixedOwnerDimacsClauses_nonzero ⟨i, hi⟩

set_option maxRecDepth 1000000 in
theorem sixTenMixedOwnerSatCnf_sat_of_constraints
    {val : DimacsValuation}
    (h : SixTenMixedOwnerConstraintSemantics val) :
    sixTenMixedOwnerSatCnf.Sat (satAssignmentOfDimacs val) := by
  simpa only [sixTenMixedOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      sixTenMixedOwnerDimacsClauses_nonzero_of_mem
      (sixTenMixedOwnerConstraintSemantics_formulaSatisfied h)

theorem sixTenMixedOwnerConstraintSemantics_false
    {val : DimacsValuation}
    (h : SixTenMixedOwnerConstraintSemantics val) : False := by
  have hsat := sixTenMixedOwnerSatCnf_sat_of_constraints h
  have hunsat := LRAT.check_sound sixTenMixedOwnerProof
    sixTenMixedOwnerSatCnf sixTenMixedOwner_check
  rw [CNF.sat_def] at hsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.sixTenMixedOwnerSatCnf_sat_of_constraints
#print axioms Erdos85.sixTenMixedOwnerConstraintSemantics_false
