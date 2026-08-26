import Proofs.Erdos85OneHighRefinementPinnedCnfSatisfaction

/-!
# Certificate-facing exclusion for refinement-pinned one-high CNFs

This is the generic socket between a structural graph carrying a fixed slot
refinement and an independently checked LRAT proof for the corresponding
generated CNF.
-/

namespace Erdos85

open Std.Tactic.BVDecide

noncomputable section

set_option maxRecDepth 1000000

/-- A structural graph satisfying the lex-prefix constraints and the fixed
slot pins supplies a Boolean model of the exact generated CNF. -/
theorem oneHighFamilyRefinementSatCnf_sat_of_constraints
    (profile : Nat) (refinement : List (List OneHighLabelPair))
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints profile R)
    (hpins : OneHighRefinementPinSemantics R refinement)
    (hnz : ∀ clause ∈
      (oneHighFamilyRefinementClauses profile refinement).clauses,
      DimacsClauseNonzero clause) :
    ∃ assignment : Nat → Bool,
      (oneHighFamilyRefinementSatCnf profile refinement).Sat assignment := by
  let initial : DimacsValuation := fun _ => false
  have hs := oneHighFamilyRefinementClausesVal_semanticSound
    R profile refinement hc hpins initial
  have hstate := oneHighFamilyRefinementClausesVal_state
    R profile refinement initial
  have hdimacs : dimacsFormulaSatisfied
      (oneHighFamilyRefinementClausesVal R profile refinement initial).2
      (oneHighFamilyRefinementClauses profile refinement).clauses := by
    exact hstate ▸ hs.satisfied
  exact ⟨satAssignmentOfDimacs
      (oneHighFamilyRefinementClausesVal R profile refinement initial).2,
    satCnf_of_dimacsFormulaSatisfied hnz hdimacs⟩

/-- Proof-grade UNSAT payload supplied by a generated certificate module. -/
structure OneHighRefinementCheckedUnsat
    (profile : Nat) (refinement : List (List OneHighLabelPair)) : Prop where
  nonzero : ∀ clause ∈
    (oneHighFamilyRefinementClauses profile refinement).clauses,
    DimacsClauseNonzero clause
  unsat : ∀ assignment : Nat → Bool,
    ¬(oneHighFamilyRefinementSatCnf profile refinement).Sat assignment

/-- Turn a successful kernel LRAT check into the reusable UNSAT payload. -/
theorem oneHighRefinementCheckedUnsat_of_lrat
    {profile : Nat} {refinement : List (List OneHighLabelPair)}
    (hnz : ∀ clause ∈
      (oneHighFamilyRefinementClauses profile refinement).clauses,
      DimacsClauseNonzero clause)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (oneHighFamilyRefinementSatCnf profile refinement)) :
    OneHighRefinementCheckedUnsat profile refinement where
  nonzero := hnz
  unsat := by
    intro assignment hsat
    rw [Std.Sat.CNF.sat_def] at hsat
    have hu := LRAT.check_sound proof
      (oneHighFamilyRefinementSatCnf profile refinement) hcheck assignment
    rw [hsat] at hu
    contradiction

/-- A checked exact refinement excludes every graph model carrying precisely
those profile constraints and pin semantics. -/
theorem false_of_oneHighRefinementCheckedUnsat
    {profile : Nat} {refinement : List (List OneHighLabelPair)}
    (hchecked : OneHighRefinementCheckedUnsat profile refinement)
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints profile R)
    (hpins : OneHighRefinementPinSemantics R refinement) : False := by
  rcases oneHighFamilyRefinementSatCnf_sat_of_constraints
    profile refinement R hc hpins hchecked.nonzero with ⟨assignment, hsat⟩
  exact hchecked.unsat assignment hsat

end

end Erdos85

#print axioms Erdos85.oneHighFamilyRefinementSatCnf_sat_of_constraints
#print axioms Erdos85.oneHighRefinementCheckedUnsat_of_lrat
#print axioms Erdos85.false_of_oneHighRefinementCheckedUnsat
