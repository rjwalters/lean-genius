import Proofs.Erdos85EightEightHighOwnerCertificate
import Proofs.Erdos85EightEightLowOwnerCnfSemantics

/-!
# Semantic socket for the variable-cross high eight-plus-eight owner CNF

The interface exposes the three structural cross-block clause families and
the guarded owner-service/common-neighbor families separately.  A graph
adapter may therefore use the actual exterior-pair relation for the active
variables without first classifying its cyclic support.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

structure EightEightHighOwnerConstraintSemantics
    (val : DimacsValuation) : Prop where
  cross_degree : ∀ clause,
    clause ∈ eightEightHighCrossDegreeClauses →
      dimacsClauseSatisfied val clause
  intertwining : ∀ clause,
    clause ∈ eightEightHighIntertwiningClauses →
      dimacsClauseSatisfied val clause
  hit_activity : ∀ clause,
    clause ∈ eightEightHighHitActivityClauses →
      dimacsClauseSatisfied val clause
  service_exists : ∀ e v,
    e < 64 → v < 16 →
      eightEightHighOwnerTargetContains e v = true →
      dimacsClauseSatisfied val
        (eightEightHighActiveGuard e ++ eightEightHighServiceVariables e v)
  service_unique : ∀ e v clause,
    e < 64 → v < 16 →
      eightEightHighOwnerTargetContains e v = true →
      clause ∈ eightEightPairwiseNegativeClauses
        (eightEightHighServiceVariables e v) →
      dimacsClauseSatisfied val clause
  internal_zero : ∀ e v x,
    e < 64 → v < 16 →
      eightEightHighOwnerTargetContains e v = false →
      x ∈ eightEightHighServiceVariables e v →
      dimacsClauseSatisfied val (eightEightHighActiveGuard e ++ [-x])
  intersecting_no_common : ∀ e f clause,
    e < f → f < 64 → eightEightHighOwnersIntersect e f = true →
      clause ∈ eightEightHighNoCommonClauses e f →
      dimacsClauseSatisfied val clause
  no_two_common : ∀ e f clause,
    e < f → f < 64 → eightEightHighOwnersIntersect e f = false →
      clause ∈ eightEightHighAtMostOneCommonClauses e f →
      dimacsClauseSatisfied val clause

theorem eightEightHighOwnerConstraintSemantics_formulaSatisfied
    {val : DimacsValuation}
    (h : EightEightHighOwnerConstraintSemantics val) :
    dimacsFormulaSatisfied val eightEightHighDimacsClauses := by
  intro clause hclause
  simp only [eightEightHighDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hprefix4 | hc4
  · rcases List.mem_append.mp hprefix4 with hprefix3 | hservice
    · rcases List.mem_append.mp hprefix3 with hprefix2 | hactivity
      · rcases List.mem_append.mp hprefix2 with hdegree | hinter
        · exact h.cross_degree clause hdegree
        · exact h.intertwining clause hinter
      · exact h.hit_activity clause hactivity
    · simp only [eightEightHighServiceClauses, List.mem_flatMap,
        List.mem_range] at hservice
      obtain ⟨e, he64, v, hv16, hclause⟩ := hservice
      split at hclause
      · next htarget =>
        rcases List.mem_append.mp hclause with hexists | hunique
        · simp only [List.mem_singleton] at hexists
          subst clause
          exact h.service_exists e v he64 hv16 (by
            simpa only [eightEightHighOwnerTargetContains] using htarget)
        · exact h.service_unique e v clause he64 hv16 (by
            simpa only [eightEightHighOwnerTargetContains] using htarget)
            hunique
      · next hnotTarget =>
        simp only [List.mem_map] at hclause
        obtain ⟨x, hx, rfl⟩ := hclause
        have hfalse : eightEightHighOwnerTargetContains e v = false := by
          apply Bool.eq_false_iff.mpr
          simpa only [eightEightHighOwnerTargetContains] using hnotTarget
        exact h.internal_zero e v x he64 hv16 hfalse hx
  · simp only [eightEightHighC4Clauses, List.mem_flatMap,
      List.mem_range, List.mem_filter] at hc4
    obtain ⟨e, he64, f, ⟨hf64, hef⟩, hclause⟩ := hc4
    split at hclause
    · next hintersect =>
      exact h.intersecting_no_common e f clause (of_decide_eq_true hef) hf64
        (by simpa using hintersect) hclause
    · next hdisjoint =>
      exact h.no_two_common e f clause (of_decide_eq_true hef) hf64
        (by simpa using hdisjoint) hclause

set_option maxHeartbeats 0 in
theorem eightEightHighOwnerDimacsClauses_all_ne_zero :
    ∀ i : Fin eightEightHighDimacsClauses.size,
      (eightEightHighDimacsClauses[i].all fun lit => lit != 0) = true := by
  native_decide

theorem eightEightHighOwnerDimacsClauses_nonzero_of_mem :
    ∀ clause ∈ eightEightHighDimacsClauses,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hclause
  subst clause
  have hne := List.all_eq_true.mp
    (eightEightHighOwnerDimacsClauses_all_ne_zero ⟨i, hi⟩) lit hlit
  simpa using hne

set_option maxRecDepth 1000000 in
theorem eightEightHighOwnerSatCnf_sat_of_constraints
    {val : DimacsValuation}
    (h : EightEightHighOwnerConstraintSemantics val) :
    eightEightHighOwnerSatCnf.Sat (satAssignmentOfDimacs val) := by
  simpa only [eightEightHighOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      eightEightHighOwnerDimacsClauses_nonzero_of_mem
      (eightEightHighOwnerConstraintSemantics_formulaSatisfied h)

theorem eightEightHighOwnerConstraintSemantics_false
    {val : DimacsValuation}
    (h : EightEightHighOwnerConstraintSemantics val) : False := by
  have hsat := eightEightHighOwnerSatCnf_sat_of_constraints h
  have hunsat := LRAT.check_sound eightEightHighOwnerProof
    eightEightHighOwnerSatCnf eightEightHighOwner_check
  rw [CNF.sat_def] at hsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.eightEightHighOwnerSatCnf_sat_of_constraints
#print axioms Erdos85.eightEightHighOwnerConstraintSemantics_false
