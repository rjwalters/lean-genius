import Proofs.Erdos85MuNegFiveCanonicalOwnerCertificate

/-!
# Semantic contradiction sockets for h504 and h512

The remaining canonical `mu = -5` formulas share four owner-clause families;
only the exact cross-fiber degree family depends on `(total,same)`.  The generic
record below is the graph-to-CNF interface, and the two endpoint theorems apply
the checked LRAT terminals.
-/

namespace Erdos85

open Std Sat

structure MuNegFiveCanonicalOwnerConstraintSemantics
    (total same : Nat) (sigma : Bool) (val : DimacsValuation) : Prop where
  cross_degree : ∀ clause ∈
    muNegFiveCanonicalCrossDegreeClauses total same sigma,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegFiveZeroThreeIntertwiningClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈ muNegFiveZeroThreeHitActivityClauses,
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈ muNegFiveZeroThreeServiceClauses,
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈ muNegFiveZeroThreeC4Clauses,
    dimacsClauseSatisfied val clause

theorem muNegFiveCanonicalOwnerConstraintSemantics_formulaSatisfied
    {total same : Nat} {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveCanonicalOwnerConstraintSemantics
      total same sigma val) :
    dimacsFormulaSatisfied val
      (muNegFiveCanonicalOwnerDimacsClauses total same sigma) := by
  intro clause hclause
  simp only [muNegFiveCanonicalOwnerDimacsClauses, List.mem_toArray] at hclause
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
theorem muNegFiveCanonicalOwnerDimacsClauses_all_ne_zero :
    (∀ sigma : Bool,
      ((muNegFiveZeroFourOwnerDimacsClauses sigma).all fun clause =>
        clause.all fun lit => lit != 0) = true) ∧
    (∀ sigma : Bool,
      ((muNegFiveOneTwoOwnerDimacsClauses sigma).all fun clause =>
        clause.all fun lit => lit != 0) = true) := by
  native_decide

theorem muNegFiveZeroFourOwnerDimacsClauses_nonzero_of_mem
    (sigma : Bool) :
    ∀ clause ∈ muNegFiveZeroFourOwnerDimacsClauses sigma,
      DimacsClauseNonzero clause := by
  have hcheck := muNegFiveCanonicalOwnerDimacsClauses_all_ne_zero.1 sigma
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  simpa using hclauseCheck lit hlit

theorem muNegFiveOneTwoOwnerDimacsClauses_nonzero_of_mem
    (sigma : Bool) :
    ∀ clause ∈ muNegFiveOneTwoOwnerDimacsClauses sigma,
      DimacsClauseNonzero clause := by
  have hcheck := muNegFiveCanonicalOwnerDimacsClauses_all_ne_zero.2 sigma
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  simpa using hclauseCheck lit hlit

theorem muNegFiveZeroFourOwnerSatCnf_sat_of_constraints
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveCanonicalOwnerConstraintSemantics 4 3 sigma val) :
    (muNegFiveZeroFourOwnerSatCnf sigma).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegFiveZeroFourOwnerSatCnf,
    muNegFiveZeroFourOwnerDimacsClauses] using
    satCnf_of_dimacsFormulaSatisfied
      (muNegFiveZeroFourOwnerDimacsClauses_nonzero_of_mem sigma)
      (muNegFiveCanonicalOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegFiveOneTwoOwnerSatCnf_sat_of_constraints
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveCanonicalOwnerConstraintSemantics 6 4 sigma val) :
    (muNegFiveOneTwoOwnerSatCnf sigma).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegFiveOneTwoOwnerSatCnf,
    muNegFiveOneTwoOwnerDimacsClauses] using
    satCnf_of_dimacsFormulaSatisfied
      (muNegFiveOneTwoOwnerDimacsClauses_nonzero_of_mem sigma)
      (muNegFiveCanonicalOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegFiveZeroFourOwnerConstraintSemantics_false
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveCanonicalOwnerConstraintSemantics 4 3 sigma val) : False := by
  have hsat := muNegFiveZeroFourOwnerSatCnf_sat_of_constraints h
  rw [CNF.sat_def] at hsat
  have hu := muNegFiveZeroFourOwner_unsat sigma (satAssignmentOfDimacs val)
  rw [hsat] at hu
  contradiction

theorem muNegFiveOneTwoOwnerConstraintSemantics_false
    {sigma : Bool} {val : DimacsValuation}
    (h : MuNegFiveCanonicalOwnerConstraintSemantics 6 4 sigma val) : False := by
  have hsat := muNegFiveOneTwoOwnerSatCnf_sat_of_constraints h
  rw [CNF.sat_def] at hsat
  have hu := muNegFiveOneTwoOwner_unsat sigma (satAssignmentOfDimacs val)
  rw [hsat] at hu
  contradiction

end Erdos85

#print axioms Erdos85.muNegFiveZeroFourOwnerConstraintSemantics_false
#print axioms Erdos85.muNegFiveOneTwoOwnerConstraintSemantics_false
