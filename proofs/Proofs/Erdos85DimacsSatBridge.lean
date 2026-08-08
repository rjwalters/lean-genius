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

/-- Translate a generated DIMACS segment clausewise. -/
def dimacsFormulaToSatClauses (formula : Array DimacsClause) :
    Array (CNF.Clause Nat) :=
  formula.map dimacsClauseToSatClause

/-- The SAT CNF assembled directly from the four verified order-49 clause
segments, in exactly the order used by the certificate generator. -/
def orderFortyNineGeneratedSatCnf (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineFixedClauses masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks 9).clauses ++
    dimacsFormulaToSatClauses (orderFortyNinePartitionClauses masks)

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

/-- Clausewise nonzeroness of the four generated DIMACS segments. -/
structure OrderFortyNineCnfSegmentsNonzero (masks : Array Nat) : Prop where
  fixed : ∀ clause ∈ orderFortyNineFixedClauses masks,
    DimacsClauseNonzero clause
  c4 : ∀ clause ∈ orderFortyNineC4Clauses,
    DimacsClauseNonzero clause
  degree : ∀ clause ∈ (orderFortyNineDegreeBlocks 9).clauses,
    DimacsClauseNonzero clause
  partition : ∀ clause ∈ orderFortyNinePartitionClauses masks,
    DimacsClauseNonzero clause

theorem orderFortyNineFixedClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineFixedClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineFixedClauses, Array.mem_append] at hclause
  rcases hclause with hhigh | hlow
  · simp only [orderFortyNineHighHighFixedClauses, List.mem_toArray,
      List.mem_map] at hhigh
    obtain ⟨ab, hab, rfl⟩ := hhigh
    simp only [List.mem_singleton] at hlit
    subst lit
    simp [orderFortyNineEdgeLiteral] <;> omega
  · simp only [orderFortyNineHighLowFixedClauses, List.mem_toArray,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hlow
    obtain ⟨y, w, rfl⟩ := hlow
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineSupportUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega

theorem orderFortyNineC4Clauses_nonzero :
    ∀ clause ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  rcases q with ⟨⟨i, j⟩, ⟨w, w'⟩⟩
  simp [orderFortyNineC4Clause] at hlit
  rcases hlit with rfl | rfl | rfl | rfl <;>
    simp [orderFortyNineEdgeLiteral] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineDegreeBlocks_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 9).clauses,
      DimacsClauseNonzero clause := by
  have hcheck :
      (orderFortyNineDegreeBlocks 9).clauses.all fun clause =>
        clause.all fun lit => lit != 0 := by
    native_decide
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem orderFortyNinePartitionClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNinePartitionClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNinePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNinePartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  simp [orderFortyNineEdgeLiteral] <;> omega

theorem orderFortyNineCnfSegments_nonzero (masks : Array Nat) :
    OrderFortyNineCnfSegmentsNonzero masks where
  fixed := orderFortyNineFixedClauses_nonzero masks
  c4 := orderFortyNineC4Clauses_nonzero
  degree := orderFortyNineDegreeBlocks_nonzero
  partition := orderFortyNinePartitionClauses_nonzero masks

/-- The CNF assembled from the Lean generators is covered by its four source
segments by construction.  No comparison with an external DIMACS file is
needed at the logical boundary. -/
theorem orderFortyNineGeneratedSatCnf_covered
    (masks : Array Nat) :
    OrderFortyNineCnfCoveredBySegments masks
      (orderFortyNineGeneratedSatCnf masks) := by
  let hnz := orderFortyNineCnfSegments_nonzero masks
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedSatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource, hnz.fixed source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource, hnz.c4 source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl
      ⟨source, hsource, hnz.degree source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr
      ⟨source, hsource, hnz.partition source hsource, rfl⟩

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

/-- Closed generator-facing entry point: the certificate is checked against
the CNF assembled directly from the four Lean segments, so no external-file
coverage hypothesis remains. -/
theorem false_of_orderFortyNine_generated_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedSatCnf masks)) : False :=
  false_of_orderFortyNine_lrat hc hzero
    (orderFortyNineGeneratedSatCnf_covered masks) proof hcheck

end Erdos85
