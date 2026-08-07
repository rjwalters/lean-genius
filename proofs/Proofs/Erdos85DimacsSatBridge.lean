import Std.Tactic.BVDecide.LRAT
import Proofs.Erdos85OrderFortyNineCnfSegments

/-!
# Semantic bridge from the order-49 DIMACS clauses to `Std.Sat.CNF`

The graph-facing development proves simultaneous satisfaction of four large
DIMACS clause families.  The trusted LRAT checker speaks instead about
`Std.Sat.CNF`.  This file isolates the small, certificate-independent bridge
between those two semantics.  It deliberately requires only that every
clause of the checked CNF is covered by one of the four generated families;
the runtime profile checker establishes the stronger ordered equality.
-/

open Std Sat

namespace Erdos85

/-- Translate the one-based signed DIMACS convention to the zero-based
literal convention used by `Std.Sat.CNF`. -/
def dimacsClauseToSatClause (clause : DimacsClause) : CNF.Clause Nat :=
  clause.map fun lit => (lit.natAbs - 1, 0 < lit)

/-- A DIMACS valuation, shifted to the zero-based identifiers of
`Std.Sat.CNF`. -/
def satAssignmentOfDimacs (val : DimacsValuation) : Nat → Bool :=
  fun id => val (id + 1)

def DimacsClauseNonzero (clause : DimacsClause) : Prop :=
  ∀ lit ∈ clause, lit ≠ 0

theorem dimacsLiteral_toSat_eval (val : DimacsValuation) {lit : Int}
    (hlit : lit ≠ 0) :
    (satAssignmentOfDimacs val (lit.natAbs - 1) == (0 < lit)) =
      dimacsLitValue val lit := by
  have habs : 0 < lit.natAbs := Int.natAbs_pos.mpr hlit
  have hshift : lit.natAbs - 1 + 1 = lit.natAbs :=
    Nat.sub_add_cancel habs
  by_cases hpos : 0 < lit
  · simp [satAssignmentOfDimacs, dimacsLitValue, hpos, hshift]
  · have hneg : lit < 0 := by omega
    simp [satAssignmentOfDimacs, dimacsLitValue, hpos, hshift]

theorem satClause_of_dimacsClauseSatisfied
    {val : DimacsValuation} {clause : DimacsClause}
    (hnz : DimacsClauseNonzero clause)
    (hsat : dimacsClauseSatisfied val clause) :
    CNF.Clause.eval (satAssignmentOfDimacs val)
      (dimacsClauseToSatClause clause) = true := by
  obtain ⟨lit, hlit, htrue⟩ := hsat
  simp only [CNF.Clause.eval, List.any_eq_true]
  refine ⟨(lit.natAbs - 1, 0 < lit), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨lit, hlit, rfl⟩
  · rw [dimacsLiteral_toSat_eval val (hnz lit hlit)]
    exact htrue

/-- Every checked clause comes from one of the four segmented order-49
families.  Including nonzeroness here makes the bridge reusable for parsed
CNFs without baking in any particular generator proof. -/
structure OrderFortyNineCnfCoveredBySegments
    (masks : Array Nat) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineFixedClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks 9).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNinePartitionClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem sat_of_orderFortyNineCnfSegmentsSatisfied_of_covered
    {masks : Array Nat} {cnf : CNF Nat} {val : DimacsValuation}
    (hsat : OrderFortyNineCnfSegmentsSatisfied masks val)
    (hcovered : OrderFortyNineCnfCoveredBySegments masks cnf) :
    cnf.Sat (satAssignmentOfDimacs val) := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro i hi
  rcases hcovered.covered cnf.clauses[i] (Array.getElem_mem hi) with
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.fixed source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.c4 source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.degree source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.partition source hsource)

/-- An LRAT-unsatisfiable CNF covering the generated segments rules out the
corresponding Boolean graph constraints. -/
theorem false_of_orderFortyNine_cnf_unsat
    {masks : Array Nat} {edges : BitVec 1176} {cnf : CNF Nat}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks)
    (hcovered : OrderFortyNineCnfCoveredBySegments masks cnf)
    (hunsat : cnf.Unsat) : False := by
  obtain ⟨val, hsegments, _⟩ :=
    orderFortyNineCnfSegments_satisfied hc hzero
  have hsat := sat_of_orderFortyNineCnfSegmentsSatisfied_of_covered
    hsegments hcovered
  rw [CNF.sat_def] at hsat
  have := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at this
  contradiction

/-- Direct entry point for a verified LRAT proof. -/
theorem false_of_orderFortyNine_lrat
    {masks : Array Nat} {edges : BitVec 1176} {cnf : CNF Nat}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks)
    (hcovered : OrderFortyNineCnfCoveredBySegments masks cnf)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof cnf) : False :=
  false_of_orderFortyNine_cnf_unsat hc hzero hcovered
    (Std.Tactic.BVDecide.LRAT.check_sound proof cnf hcheck)

end Erdos85
