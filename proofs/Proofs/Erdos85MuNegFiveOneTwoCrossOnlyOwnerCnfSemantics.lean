import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerCertificate

/-! # Semantic contradiction socket for the corrected cross-only h512 CNF -/

namespace Erdos85

open Std Sat

structure MuNegFiveOneTwoCrossOnlyOwnerConstraintSemantics
    (sigma : Bool) (val : DimacsValuation) : Prop where
  cross_degree : ∀ clause ∈ muNegFiveCanonicalCrossDegreeClauses 6 4 sigma,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegFiveZeroThreeIntertwiningClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈ muNegFiveOneTwoCrossOnlyHitActivityClauses,
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈ muNegFiveOneTwoCrossOnlyServiceClauses,
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈ muNegFiveOneTwoCrossOnlyC4Clauses,
    dimacsClauseSatisfied val clause

theorem muNegFiveOneTwoCrossOnlyOwnerConstraintSemantics_formulaSatisfied
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveOneTwoCrossOnlyOwnerConstraintSemantics sigma val) :
    dimacsFormulaSatisfied val
      (muNegFiveOneTwoCrossOnlyOwnerDimacsClauses sigma) := by
  intro clause hclause
  simp only [muNegFiveOneTwoCrossOnlyOwnerDimacsClauses,
    List.mem_toArray] at hclause
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
theorem muNegFiveOneTwoCrossOnlyOwnerDimacsClauses_all_ne_zero :
    ∀ sigma : Bool,
      ((muNegFiveOneTwoCrossOnlyOwnerDimacsClauses sigma).all fun clause ↦
        clause.all fun lit ↦ lit != 0) = true := by
  native_decide

theorem muNegFiveOneTwoCrossOnlyOwnerDimacsClauses_nonzero_of_mem
    (sigma : Bool) :
    ∀ clause ∈ muNegFiveOneTwoCrossOnlyOwnerDimacsClauses sigma,
      DimacsClauseNonzero clause := by
  have hcheck := muNegFiveOneTwoCrossOnlyOwnerDimacsClauses_all_ne_zero sigma
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem muNegFiveOneTwoCrossOnlyOwnerSatCnf_sat_of_constraints
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveOneTwoCrossOnlyOwnerConstraintSemantics sigma val) :
    (muNegFiveOneTwoCrossOnlyOwnerSatCnf sigma).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegFiveOneTwoCrossOnlyOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerDimacsClauses_nonzero_of_mem sigma)
      (muNegFiveOneTwoCrossOnlyOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegFiveOneTwoCrossOnlyOwnerConstraintSemantics_false
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveOneTwoCrossOnlyOwnerConstraintSemantics sigma val) : False := by
  have hsat := muNegFiveOneTwoCrossOnlyOwnerSatCnf_sat_of_constraints h
  rw [CNF.sat_def] at hsat
  have hu := muNegFiveOneTwoCrossOnlyOwner_unsat sigma
    (satAssignmentOfDimacs val)
  rw [hsat] at hu
  contradiction

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwnerConstraintSemantics_false
