import Proofs.Erdos85EightEightBothTriangleOwnerCertificate
import Proofs.Erdos85EightEightLowOwnerCnfSemantics

/-!
# Semantic socket for the both-all-triangle eight-plus-eight owner CNF

The four fields expose exactly the service and C4 consequences needed by
the generated clause families.  All finite bookkeeping and the checked
LRAT contradiction are discharged below.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

set_option maxHeartbeats 0

structure EightEightBothTriangleOwnerConstraintSemantics
    (val : DimacsValuation) : Prop where
  service_exists : ∀ e v,
    e < 48 → v < 16 → eightEightBothTriangleOwnerTargetContains e v = true →
      dimacsClauseSatisfied val (eightEightBothTriangleOwnerServiceVariables e v)
  service_unique : ∀ e v clause,
    e < 48 → v < 16 → eightEightBothTriangleOwnerTargetContains e v = true →
      clause ∈ eightEightPairwiseNegativeClauses
        (eightEightBothTriangleOwnerServiceVariables e v) →
      dimacsClauseSatisfied val clause
  intersecting_no_common : ∀ e f clause,
    e < f → f < 48 → eightEightBothTriangleOwnersIntersect e f = true →
      clause ∈ eightEightBothTriangleOwnerNoCommonClauses e f →
      dimacsClauseSatisfied val clause
  no_two_common : ∀ e f clause,
    e < f → f < 48 → eightEightBothTriangleOwnersIntersect e f = false →
      clause ∈ eightEightBothTriangleOwnerAtMostOneCommonClauses e f →
      dimacsClauseSatisfied val clause

theorem eightEightBothTriangleOwnerConstraintSemantics_formulaSatisfied
    {val : DimacsValuation}
    (h : EightEightBothTriangleOwnerConstraintSemantics val) :
    dimacsFormulaSatisfied val eightEightBothTriangleOwnerDimacsClauses := by
  intro clause hclause
  simp only [eightEightBothTriangleOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hservice | hc4
  · simp only [eightEightBothTriangleOwnerServiceClauses, List.mem_flatMap,
      List.mem_range] at hservice
    obtain ⟨e, he48, v, hv16, hclause⟩ := hservice
    split at hclause
    · next htarget =>
      rcases List.mem_append.mp hclause with hexists | hunique
      · simp only [List.mem_singleton] at hexists
        subst clause
        exact h.service_exists e v he48 hv16 (by
          simpa only [eightEightBothTriangleOwnerTargetContains] using htarget)
      · exact h.service_unique e v clause he48 hv16 (by
          simpa only [eightEightBothTriangleOwnerTargetContains] using htarget)
          hunique
    · simp at hclause
  · simp only [eightEightBothTriangleOwnerC4Clauses, List.mem_flatMap,
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
theorem eightEightBothTriangleOwnerDimacsClauses_all_ne_zero :
    ∀ i : Fin eightEightBothTriangleOwnerDimacsClauses.size,
      (eightEightBothTriangleOwnerDimacsClauses[i].all fun lit => lit != 0) = true := by
  native_decide

theorem eightEightBothTriangleOwnerDimacsClauses_nonzero
    (i : Fin eightEightBothTriangleOwnerDimacsClauses.size) :
    DimacsClauseNonzero eightEightBothTriangleOwnerDimacsClauses[i] := by
  intro lit hlit
  have hne := List.all_eq_true.mp
    (eightEightBothTriangleOwnerDimacsClauses_all_ne_zero i) lit hlit
  simpa using hne

theorem eightEightBothTriangleOwnerDimacsClauses_nonzero_of_mem :
    ∀ clause ∈ eightEightBothTriangleOwnerDimacsClauses,
      DimacsClauseNonzero clause := by
  intro clause hclause
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hclause
  rw [← heq]
  exact eightEightBothTriangleOwnerDimacsClauses_nonzero ⟨i, hi⟩

set_option maxRecDepth 1000000 in
theorem eightEightBothTriangleOwnerSatCnf_sat_of_constraints
    {val : DimacsValuation}
    (h : EightEightBothTriangleOwnerConstraintSemantics val) :
    eightEightBothTriangleOwnerSatCnf.Sat (satAssignmentOfDimacs val) := by
  simpa only [eightEightBothTriangleOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      eightEightBothTriangleOwnerDimacsClauses_nonzero_of_mem
      (eightEightBothTriangleOwnerConstraintSemantics_formulaSatisfied h)

theorem eightEightBothTriangleOwnerConstraintSemantics_false
    {val : DimacsValuation}
    (h : EightEightBothTriangleOwnerConstraintSemantics val) : False := by
  have hsat := eightEightBothTriangleOwnerSatCnf_sat_of_constraints h
  have hunsat := LRAT.check_sound eightEightBothTriangleOwnerProof
    eightEightBothTriangleOwnerSatCnf eightEightBothTriangleOwner_check
  rw [CNF.sat_def] at hsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.eightEightBothTriangleOwnerSatCnf_sat_of_constraints
#print axioms Erdos85.eightEightBothTriangleOwnerConstraintSemantics_false
