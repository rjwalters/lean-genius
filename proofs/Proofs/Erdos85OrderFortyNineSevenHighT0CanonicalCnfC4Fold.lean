import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfC4Witness

/-!
# Clause plumbing for the compact canonical H7/T0 C4 fold

This module converts the graph-level missing-edge witness into satisfaction
of the generator's filtered negative-variable clause.
-/

namespace Erdos85

/-- If a status occurring in a C4 status list evaluates false, is not a
fixed-false status, and every variable status has a positive identifier, its
negative literal occurs in the filtered generator clause and is true. -/
theorem sevenHighT0CanonicalC4Clause_satisfied_of_false_status
    (val : DimacsValuation)
    (statuses : List SevenHighT0CanonicalEdgeStatus)
    (status : SevenHighT0CanonicalEdgeStatus)
    (hmem : status ∈ statuses)
    (hnotFalse : status ≠ .fixedFalse)
    (hvalue : sevenHighT0CanonicalEdgeStatusValue val status = false)
    (hpositive : ∀ id, status = .variable id → 0 < id) :
    dimacsClauseSatisfied val
      (statuses.filterMap sevenHighT0CanonicalC4Literal) := by
  cases status with
  | fixedFalse => exact (hnotFalse rfl).elim
  | fixedTrue => simp [sevenHighT0CanonicalEdgeStatusValue] at hvalue
  | «variable» id =>
      have hid : 0 < id := hpositive id rfl
      refine ⟨-(id : Int), ?_, ?_⟩
      · apply List.mem_filterMap.mpr
        exact ⟨.variable id, hmem, rfl⟩
      · have hval : val id = false := by
          simpa [sevenHighT0CanonicalEdgeStatusValue] using hvalue
        simp [dimacsLitValue, hval, show ¬ (id : Int) < 0 by omega]

/-- Every actual variable edge status emitted by the canonical generator has
a positive one-based identifier. -/
theorem sevenHighT0CanonicalEdgeStatus_variable_pos
    (a b id : Nat)
    (hstatus : sevenHighT0CanonicalEdgeStatus a b = .variable id) :
    0 < id := by
  unfold sevenHighT0CanonicalEdgeStatus at hstatus
  split at hstatus <;> try contradiction
  split at hstatus
  · simp only [SevenHighT0CanonicalEdgeStatus.variable.injEq] at hstatus
    rw [← hstatus]
    simp [sevenHighT0CanonicalLowEdgeId]
  · split at hstatus <;> try contradiction
    split at hstatus <;> try contradiction
    split at hstatus <;> try contradiction
    split at hstatus <;> contradiction

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalC4Clause_satisfied_of_false_status
#print axioms Erdos85.sevenHighT0CanonicalEdgeStatus_variable_pos
