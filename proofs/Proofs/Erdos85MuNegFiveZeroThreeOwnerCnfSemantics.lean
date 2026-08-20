import Proofs.Erdos85MuNegFiveZeroThreeOwnerCertificate

/-!
# Semantic contradiction socket for the h503 owner CNF

Graph-facing code can establish the five generated clause families separately.
This file assembles those fields, bridges DIMACS satisfaction to `Std.Sat.CNF`,
and applies the checked two-phase LRAT terminal.
-/

namespace Erdos85

open Std Sat

structure MuNegFiveZeroThreeOwnerConstraintSemantics
    (sigma : Bool) (val : DimacsValuation) : Prop where
  cross_degree : ∀ clause ∈ muNegFiveZeroThreeCrossDegreeClauses sigma,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegFiveZeroThreeIntertwiningClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈ muNegFiveZeroThreeHitActivityClauses,
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈ muNegFiveZeroThreeServiceClauses,
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈ muNegFiveZeroThreeC4Clauses,
    dimacsClauseSatisfied val clause

theorem muNegFiveZeroThreeOwnerConstraintSemantics_formulaSatisfied
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveZeroThreeOwnerConstraintSemantics sigma val) :
    dimacsFormulaSatisfied val
      (muNegFiveZeroThreeDimacsClauses sigma) := by
  intro clause hclause
  simp only [muNegFiveZeroThreeDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · rcases List.mem_append.mp hclause with hclause | hclause
    · rcases List.mem_append.mp hclause with hclause | hclause
      · rcases List.mem_append.mp hclause with hdegree | hintertwining
        · exact h.cross_degree clause hdegree
        · exact h.intertwining clause hintertwining
      · exact h.hit_activity clause hclause
    · exact h.service clause hclause
  · exact h.exterior_c4 clause hclause

set_option maxHeartbeats 0 in
theorem muNegFiveZeroThreeOwnerDimacsClauses_all_ne_zero :
    ∀ sigma : Bool,
      ((muNegFiveZeroThreeDimacsClauses sigma).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

theorem muNegFiveZeroThreeOwnerDimacsClauses_nonzero_of_mem
    (sigma : Bool) :
    ∀ clause ∈ muNegFiveZeroThreeDimacsClauses sigma,
      DimacsClauseNonzero clause := by
  have hcheck := muNegFiveZeroThreeOwnerDimacsClauses_all_ne_zero sigma
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem muNegFiveZeroThreeOwnerSatCnf_sat_of_constraints
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveZeroThreeOwnerConstraintSemantics sigma val) :
    (muNegFiveZeroThreeSatCnf sigma).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegFiveZeroThreeSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      (muNegFiveZeroThreeOwnerDimacsClauses_nonzero_of_mem sigma)
      (muNegFiveZeroThreeOwnerConstraintSemantics_formulaSatisfied h)

/-- No valuation can realize all five h503 owner-clause families. -/
theorem muNegFiveZeroThreeOwnerConstraintSemantics_false
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveZeroThreeOwnerConstraintSemantics sigma val) : False := by
  have hsat := muNegFiveZeroThreeOwnerSatCnf_sat_of_constraints h
  rw [CNF.sat_def] at hsat
  have hu := muNegFiveZeroThreeOwner_unsat sigma
    (satAssignmentOfDimacs val)
  rw [hsat] at hu
  contradiction

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeOwnerConstraintSemantics_false
