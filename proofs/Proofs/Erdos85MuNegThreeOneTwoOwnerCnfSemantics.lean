import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificates

/-!
# Semantic socket for the μ=-3 `(1,2)` owner-grid CNFs

The seven fields mirror the seven clause families in the checked generator.
Graph-to-CNF embeddings can establish the families independently and use the
single contradiction theorem below.
-/

namespace Erdos85

open Std Sat

structure MuNegThreeOneTwoOwnerConstraintSemantics
    (fwd : Bool) (c : Nat) (val : DimacsValuation) : Prop where
  fixed : ∀ clause ∈ muNegThreeFixClauses fwd c,
    dimacsClauseSatisfied val clause
  opposite_rows : ∀ clause ∈ muNegThreeOppRowClauses,
    dimacsClauseSatisfied val clause
  opposite_columns : ∀ clause ∈ muNegThreeOppColClauses,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegThreeIntertwineClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈ muNegThreeHitActivityClauses,
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈ muNegThreeServiceClauses,
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈ muNegThreeC4Clauses,
    dimacsClauseSatisfied val clause

theorem muNegThreeOneTwoOwnerConstraintSemantics_formulaSatisfied
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) :
    dimacsFormulaSatisfied val
      (muNegThreeOneTwoOwnerDimacsClauses fwd c) := by
  intro clause hclause
  simp only [muNegThreeOneTwoOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · rcases List.mem_append.mp hclause with hclause | hclause
    · rcases List.mem_append.mp hclause with hclause | hclause
      · rcases List.mem_append.mp hclause with hclause | hclause
        · rcases List.mem_append.mp hclause with hclause | hclause
          · rcases List.mem_append.mp hclause with hfixed | hrows
            · exact h.fixed clause hfixed
            · exact h.opposite_rows clause hrows
          · exact h.opposite_columns clause hclause
        · exact h.intertwining clause hclause
      · exact h.hit_activity clause hclause
    · exact h.service clause hclause
  · exact h.exterior_c4 clause hclause

theorem muNegThreeOneTwoOwnerSatCnf_sat_of_constraints
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hnz : ∀ clause ∈ muNegThreeOneTwoOwnerDimacsClauses fwd c,
      DimacsClauseNonzero clause)
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) :
    (muNegThreeOneTwoOwnerSatCnf fwd c).Sat (satAssignmentOfDimacs val) := by
  simpa only [muNegThreeOneTwoOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied hnz
      (muNegThreeOneTwoOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegThreeOneTwoOwnerConstraintSemantics_false
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6)
    (hnz : ∀ clause ∈ muNegThreeOneTwoOwnerDimacsClauses fwd c,
      DimacsClauseNonzero clause)
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) : False := by
  have hsat := muNegThreeOneTwoOwnerSatCnf_sat_of_constraints hnz h
  rw [CNF.sat_def] at hsat
  have hfalse := muNegThreeOneTwoOwnerSatCnf_unsat fwd c hc
    (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwnerConstraintSemantics_false
