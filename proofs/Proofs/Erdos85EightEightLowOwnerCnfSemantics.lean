import Proofs.Erdos85EightEightLowOwnerCertificate

/-!
# Semantic socket for the low eight-plus-eight owner CNF

This file separates the finite generator bookkeeping from the graph-facing
owner transport.  A caller supplies a DIMACS valuation together with the
four exact clause consequences of service existence, service uniqueness,
intersecting-owner C4 exclusion, and ordinary C4 exclusion.  The generated
CNF is then satisfied, contradicting the checked LRAT certificate.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

set_option maxHeartbeats 0

/-- Generator-facing semantic interface.  Its four fields correspond
directly to the four high-level fields of `OutsideCClauseSemantics`; all
remaining list/array bookkeeping is discharged below. -/
structure EightEightLowOwnerConstraintSemantics
    (val : DimacsValuation) : Prop where
  service_exists : ∀ e v,
    e < 48 → v < 16 → eightEightOwnerTargetContains e v = true →
      dimacsClauseSatisfied val (eightEightOwnerServiceVariables e v)
  service_unique : ∀ e v clause,
    e < 48 → v < 16 → eightEightOwnerTargetContains e v = true →
      clause ∈ eightEightPairwiseNegativeClauses
        (eightEightOwnerServiceVariables e v) →
      dimacsClauseSatisfied val clause
  intersecting_no_common : ∀ e f clause,
    e < f → f < 48 → eightEightOwnersIntersect e f = true →
      clause ∈ eightEightOwnerNoCommonClauses e f →
      dimacsClauseSatisfied val clause
  no_two_common : ∀ e f clause,
    e < f → f < 48 → eightEightOwnersIntersect e f = false →
      clause ∈ eightEightOwnerAtMostOneCommonClauses e f →
      dimacsClauseSatisfied val clause

theorem eightEightLowOwnerConstraintSemantics_formulaSatisfied
    {val : DimacsValuation}
    (h : EightEightLowOwnerConstraintSemantics val) :
    dimacsFormulaSatisfied val eightEightLowOwnerDimacsClauses := by
  intro clause hclause
  simp only [eightEightLowOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hservice | hc4
  · simp only [eightEightOwnerServiceClauses, List.mem_flatMap,
      List.mem_range] at hservice
    obtain ⟨e, he48, v, hv16, hclause⟩ := hservice
    split at hclause
    · next htarget =>
      rcases List.mem_append.mp hclause with hexists | hunique
      · simp only [List.mem_singleton] at hexists
        subst clause
        exact h.service_exists e v he48 hv16 (by
          simpa only [eightEightOwnerTargetContains] using htarget)
      · exact h.service_unique e v clause he48 hv16 (by
          simpa only [eightEightOwnerTargetContains] using htarget)
          hunique
    · simp at hclause
  · simp only [eightEightOwnerC4Clauses, List.mem_flatMap,
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
theorem eightEightLowOwnerDimacsClauses_all_ne_zero :
    ∀ i : Fin eightEightLowOwnerDimacsClauses.size,
      (eightEightLowOwnerDimacsClauses[i].all fun lit => lit != 0) = true := by
  native_decide

theorem eightEightLowOwnerDimacsClauses_nonzero
    (i : Fin eightEightLowOwnerDimacsClauses.size) :
    DimacsClauseNonzero eightEightLowOwnerDimacsClauses[i] := by
  intro lit hlit
  have hne := List.all_eq_true.mp
    (eightEightLowOwnerDimacsClauses_all_ne_zero i) lit hlit
  simpa using hne

theorem satCnf_of_dimacsFormulaSatisfied
    {formula : Array DimacsClause} {val : DimacsValuation}
    (hnz : ∀ clause ∈ formula, DimacsClauseNonzero clause)
    (hsat : dimacsFormulaSatisfied val formula) :
    (show CNF Nat from ⟨dimacsFormulaToSatClauses formula⟩).Sat
      (satAssignmentOfDimacs val) := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro i hi
  change CNF.Clause.eval (satAssignmentOfDimacs val)
    (dimacsFormulaToSatClauses formula)[i] = true
  have hmem : (dimacsFormulaToSatClauses formula)[i] ∈
      dimacsFormulaToSatClauses formula := Array.getElem_mem hi
  simp only [dimacsFormulaToSatClauses, Array.mem_map] at hmem
  obtain ⟨source, hsource, heq⟩ := hmem
  simp only [dimacsFormulaToSatClauses]
  rw [← heq]
  exact satClause_of_dimacsClauseSatisfied
    (hnz source hsource) (hsat source hsource)

theorem eightEightLowOwnerDimacsClauses_nonzero_of_mem :
    ∀ clause ∈ eightEightLowOwnerDimacsClauses,
      DimacsClauseNonzero clause := by
  intro clause hclause
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hclause
  rw [← heq]
  exact eightEightLowOwnerDimacsClauses_nonzero ⟨i, hi⟩

set_option maxRecDepth 1000000 in
/-- The canonical generated SAT instance is satisfied by every valuation
meeting the abstract owner constraints. -/
theorem eightEightLowOwnerSatCnf_sat_of_constraints
    {val : DimacsValuation}
    (h : EightEightLowOwnerConstraintSemantics val) :
    eightEightLowOwnerSatCnf.Sat (satAssignmentOfDimacs val) := by
  simpa only [eightEightLowOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      eightEightLowOwnerDimacsClauses_nonzero_of_mem
      (eightEightLowOwnerConstraintSemantics_formulaSatisfied h)

/-- Checked finite contradiction exposed through the semantic interface. -/
theorem eightEightLowOwnerConstraintSemantics_false
    {val : DimacsValuation}
    (h : EightEightLowOwnerConstraintSemantics val) : False := by
  have hsat := eightEightLowOwnerSatCnf_sat_of_constraints h
  have hunsat := LRAT.check_sound eightEightLowOwnerProof
    eightEightLowOwnerSatCnf eightEightLowOwner_check
  rw [CNF.sat_def] at hsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.eightEightLowOwnerSatCnf_sat_of_constraints
#print axioms Erdos85.eightEightLowOwnerConstraintSemantics_false
