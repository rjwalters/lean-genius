import Proofs.Erdos85SixTenAllTfOwnerCertificate
import Proofs.Erdos85EightEightLowOwnerCnfSemantics

/-!
# Semantic socket for the both-all-TF 6+10 owner CNF

Mirror of `Erdos85EightEightMixedOwnerCnfSemantics` for the both-all-TF
6+10 owner terminal `a3f54ca53d`.  The four fields expose exactly the
service and C4 consequences needed by the generated clause families;
all finite bookkeeping and the checked LRAT contradiction are
discharged below.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

set_option maxHeartbeats 0

structure SixTenAllTfOwnerConstraintSemantics
    (val : DimacsValuation) : Prop where
  service_exists : ∀ e v,
    e < 48 → v < 16 → sixTenAllTfOwnerTargetContains e v = true →
      dimacsClauseSatisfied val (sixTenAllTfOwnerServiceVariables e v)
  service_unique : ∀ e v clause,
    e < 48 → v < 16 → sixTenAllTfOwnerTargetContains e v = true →
      clause ∈ sixTenPairwiseNegativeClauses
        (sixTenAllTfOwnerServiceVariables e v) →
      dimacsClauseSatisfied val clause
  intersecting_no_common : ∀ e f clause,
    e < f → f < 48 → sixTenAllTfOwnersIntersect e f = true →
      clause ∈ sixTenAllTfOwnerNoCommonClauses e f →
      dimacsClauseSatisfied val clause
  no_two_common : ∀ e f clause,
    e < f → f < 48 → sixTenAllTfOwnersIntersect e f = false →
      clause ∈ sixTenAllTfOwnerAtMostOneCommonClauses e f →
      dimacsClauseSatisfied val clause

theorem sixTenAllTfOwnerConstraintSemantics_formulaSatisfied
    {val : DimacsValuation}
    (h : SixTenAllTfOwnerConstraintSemantics val) :
    dimacsFormulaSatisfied val sixTenAllTfOwnerDimacsClauses := by
  intro clause hclause
  simp only [sixTenAllTfOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hservice | hc4
  · simp only [sixTenAllTfOwnerServiceClauses, List.mem_flatMap,
      List.mem_range] at hservice
    obtain ⟨e, he48, v, hv16, hclause⟩ := hservice
    split at hclause
    · next htarget =>
      rcases List.mem_append.mp hclause with hexists | hunique
      · simp only [List.mem_singleton] at hexists
        subst clause
        exact h.service_exists e v he48 hv16 (by
          simpa only [sixTenAllTfOwnerTargetContains] using htarget)
      · exact h.service_unique e v clause he48 hv16 (by
          simpa only [sixTenAllTfOwnerTargetContains] using htarget)
          hunique
    · simp at hclause
  · simp only [sixTenAllTfOwnerC4Clauses, List.mem_flatMap,
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
theorem sixTenAllTfOwnerDimacsClauses_all_ne_zero :
    ∀ i : Fin sixTenAllTfOwnerDimacsClauses.size,
      (sixTenAllTfOwnerDimacsClauses[i].all fun lit => lit != 0) = true := by
  native_decide

theorem sixTenAllTfOwnerDimacsClauses_nonzero
    (i : Fin sixTenAllTfOwnerDimacsClauses.size) :
    DimacsClauseNonzero sixTenAllTfOwnerDimacsClauses[i] := by
  intro lit hlit
  have hne := List.all_eq_true.mp
    (sixTenAllTfOwnerDimacsClauses_all_ne_zero i) lit hlit
  simpa using hne

theorem sixTenAllTfOwnerDimacsClauses_nonzero_of_mem :
    ∀ clause ∈ sixTenAllTfOwnerDimacsClauses,
      DimacsClauseNonzero clause := by
  intro clause hclause
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hclause
  rw [← heq]
  exact sixTenAllTfOwnerDimacsClauses_nonzero ⟨i, hi⟩

set_option maxRecDepth 1000000 in
theorem sixTenAllTfOwnerSatCnf_sat_of_constraints
    {val : DimacsValuation}
    (h : SixTenAllTfOwnerConstraintSemantics val) :
    sixTenAllTfOwnerSatCnf.Sat (satAssignmentOfDimacs val) := by
  simpa only [sixTenAllTfOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      sixTenAllTfOwnerDimacsClauses_nonzero_of_mem
      (sixTenAllTfOwnerConstraintSemantics_formulaSatisfied h)

theorem sixTenAllTfOwnerConstraintSemantics_false
    {val : DimacsValuation}
    (h : SixTenAllTfOwnerConstraintSemantics val) : False := by
  have hsat := sixTenAllTfOwnerSatCnf_sat_of_constraints h
  have hunsat := LRAT.check_sound sixTenAllTfOwnerProof
    sixTenAllTfOwnerSatCnf sixTenAllTfOwner_check
  rw [CNF.sat_def] at hsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.sixTenAllTfOwnerSatCnf_sat_of_constraints
#print axioms Erdos85.sixTenAllTfOwnerConstraintSemantics_false
