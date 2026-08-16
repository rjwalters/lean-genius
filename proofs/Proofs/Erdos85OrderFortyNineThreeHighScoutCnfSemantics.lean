import Proofs.Erdos85OrderFortyNineThreeHighScoutCnf
import Proofs.Erdos85OrderFortyNineDegreeBlocksNonzero

/-!
# Semantics for normalized three-high scout CNFs

The normalized scout formulas insert a geometry segment between the fixed
support clauses and the universal C4/degree/partition segments.  This file
isolates the generic soundness argument: any Boolean graph assignment which
satisfies those geometry units satisfies the exact generated scout CNF, so a
checked LRAT refutation excludes it.
-/

namespace Erdos85

open Std Sat

structure OrderFortyNineThreeHighScoutCnfCovered
    (masks : Array Nat) (geometry : Array DimacsClause) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineVariableFixedClauses (3 : Fin 50) masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ geometry,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks 3).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineVariablePartitionClauses (3 : Fin 50) masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem orderFortyNineDegreeBlocks_three_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 3).clauses,
      DimacsClauseNonzero clause :=
  orderFortyNineDegreeBlocks_nonzero_all 3

theorem orderFortyNineGeneratedThreeHighScoutCnf_covered
    (masks : Array Nat) (geometry : Array DimacsClause)
    (hgeometry : ∀ clause ∈ geometry, DimacsClauseNonzero clause) :
    OrderFortyNineThreeHighScoutCnfCovered masks geometry
      (orderFortyNineGeneratedThreeHighScoutCnf masks geometry) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedThreeHighScoutCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with (((hfixed | hgeometry') | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineVariableFixedClauses_nonzero _ masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hgeometry'
    exact Or.inr <| Or.inl ⟨source, hsource, hgeometry source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_three_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineVariablePartitionClauses_nonzero _ masks source hsource, rfl⟩

theorem sat_of_orderFortyNineThreeHighScoutSegments
    {masks : Array Nat} {geometry : Array DimacsClause} {cnf : CNF Nat}
    {val : DimacsValuation}
    (hsegments : OrderFortyNineVariableCnfSegmentsSatisfied
      (3 : Fin 50) masks val)
    (hgeometrySat : dimacsFormulaSatisfied val geometry)
    (hcovered : OrderFortyNineThreeHighScoutCnfCovered masks geometry cnf) :
    cnf.Sat (satAssignmentOfDimacs val) := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro i hi
  rcases hcovered.covered cnf.clauses[i] (Array.getElem_mem hi) with
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsegments.fixed source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hgeometrySat source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsegments.c4 source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsegments.degree source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsegments.partition source hsource)

theorem false_of_orderFortyNine_generated_h3_scout_lrat
    {masks : Array Nat} {geometry : Array DimacsClause} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50) masks)
    (hgeometryNonzero : ∀ clause ∈ geometry, DimacsClauseNonzero clause)
    (hgeometryBounded : dimacsFormulaBounded 1176 geometry)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges) geometry)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedThreeHighScoutCnf masks geometry)) : False := by
  obtain ⟨val, hsegments, hagree⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hgeometrySat' : dimacsFormulaSatisfied val geometry :=
    dimacsFormulaSatisfied_of_bounded_agree hgeometrySat hgeometryBounded
      (fun id hid => (hagree id hid).symm)
  have hsat := sat_of_orderFortyNineThreeHighScoutSegments hsegments
    hgeometrySat'
    (orderFortyNineGeneratedThreeHighScoutCnf_covered masks geometry
      hgeometryNonzero)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

private theorem dimacsFormulaNonzero_of_all
    {clauses : Array DimacsClause}
    (hcheck : clauses.all fun clause => clause.all fun lit => lit != 0) :
    ∀ clause ∈ clauses, DimacsClauseNonzero clause := by
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  simpa using hclauseCheck lit hlit

private theorem dimacsFormulaBounded_of_all
    {top : Nat} {clauses : Array DimacsClause}
    (hcheck : clauses.all fun clause =>
      clause.all fun lit => lit.natAbs ≤ top) :
    dimacsFormulaBounded top clauses := by
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  exact of_decide_eq_true (hclauseCheck lit hlit)

private theorem orderFortyNinePinnedMatchingClauses_nonzero
    (vertices : List (Fin 49)) (matching : List (Fin 49 × Fin 49)) :
    ∀ clause ∈ orderFortyNinePinnedMatchingClauses vertices matching,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNinePinnedMatchingClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, _hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  split <;> simp [orderFortyNineEdgeLiteral] <;> omega

private theorem orderFortyNinePinnedMatchingClauses_bounded
    (vertices : List (Fin 49)) (matching : List (Fin 49 × Fin 49)) :
    dimacsFormulaBounded 1176
      (orderFortyNinePinnedMatchingClauses vertices matching) := by
  intro clause hclause lit hlit
  simp only [orderFortyNinePinnedMatchingClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  have hne : ab.1 ≠ ab.2 := by
    exact _root_.ne_of_lt (orderFortyNineStrictPairs_lt hab)
  have hlt := orderFortyNineEdgeIndex_lt ab.1 ab.2 hne
  split <;> simp [orderFortyNineEdgeLiteral] <;> omega

private theorem orderFortyNineConditionalEdgeUnitClauses_nonzero
    (i : Fin 49) (vertices : List (Fin 49)) (p : Fin 49 → Prop)
    [DecidablePred p] (hne : ∀ z ∈ vertices, i ≠ z) :
    ∀ clause ∈ (vertices.map fun z =>
      [if p z then orderFortyNineEdgeLiteral i z
        else -orderFortyNineEdgeLiteral i z]).toArray,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [List.mem_toArray, List.mem_map] at hclause
  obtain ⟨z, hz, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  split <;> simp [orderFortyNineEdgeLiteral, hne z hz] <;> omega

private theorem orderFortyNineConditionalEdgeUnitClauses_bounded
    (i : Fin 49) (vertices : List (Fin 49)) (p : Fin 49 → Prop)
    [DecidablePred p] (hne : ∀ z ∈ vertices, i ≠ z) :
    dimacsFormulaBounded 1176 (vertices.map fun z =>
      [if p z then orderFortyNineEdgeLiteral i z
        else -orderFortyNineEdgeLiteral i z]).toArray := by
  intro clause hclause lit hlit
  simp only [List.mem_toArray, List.mem_map] at hclause
  obtain ⟨z, hz, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  have hlt := orderFortyNineEdgeIndex_lt i z (hne z hz)
  split <;> simp [orderFortyNineEdgeLiteral] <;> omega

private theorem dimacsFormulaNonzero_append
    {a b : Array DimacsClause}
    (ha : ∀ clause ∈ a, DimacsClauseNonzero clause)
    (hb : ∀ clause ∈ b, DimacsClauseNonzero clause) :
    ∀ clause ∈ a ++ b, DimacsClauseNonzero clause := by
  intro clause hclause
  rcases Array.mem_append.mp hclause with h | h
  · exact ha clause h
  · exact hb clause h

theorem orderFortyNineThreeHighDistTwoGeometryClauses_nonzero :
    ∀ clause ∈ orderFortyNineThreeHighDistTwoGeometryClauses,
      DimacsClauseNonzero clause := by
  apply dimacsFormulaNonzero_append
  · apply dimacsFormulaNonzero_append
    · apply dimacsFormulaNonzero_append <;>
        apply orderFortyNinePinnedMatchingClauses_nonzero
    · apply orderFortyNinePinnedMatchingClauses_nonzero
  · intro clause hclause lit hlit
    exact orderFortyNineConditionalEdgeUnitClauses_nonzero
      3 [13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
        38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48] (fun z => z = 13)
      (by intro z hz heq; subst z; simp at hz)
      clause (by simpa [orderFortyNineThreeHighDistTwoRootEmptyClauses]
        using hclause) lit hlit

theorem orderFortyNineThreeHighDistOneC2GeometryClauses_nonzero :
    ∀ clause ∈ orderFortyNineThreeHighDistOneC2GeometryClauses,
      DimacsClauseNonzero clause := by
  apply dimacsFormulaNonzero_append
  · apply dimacsFormulaNonzero_append <;>
      apply orderFortyNinePinnedMatchingClauses_nonzero
  · apply orderFortyNinePinnedMatchingClauses_nonzero

theorem orderFortyNineThreeHighDistOneB1GeometryClauses_nonzero :
    ∀ clause ∈ orderFortyNineThreeHighDistOneB1GeometryClauses,
      DimacsClauseNonzero clause := by
  apply dimacsFormulaNonzero_append
  · apply dimacsFormulaNonzero_append <;>
      apply orderFortyNinePinnedMatchingClauses_nonzero
  · apply orderFortyNinePinnedMatchingClauses_nonzero

theorem orderFortyNineThreeHighDistOneC1GeometryClauses_nonzero :
    ∀ clause ∈ orderFortyNineThreeHighDistOneC1GeometryClauses,
      DimacsClauseNonzero clause := by
  apply dimacsFormulaNonzero_append
  · apply dimacsFormulaNonzero_append <;>
      apply orderFortyNinePinnedMatchingClauses_nonzero
  · apply orderFortyNinePinnedMatchingClauses_nonzero

theorem orderFortyNineThreeHighDistTwoGeometryClauses_bounded :
    dimacsFormulaBounded 1176
      orderFortyNineThreeHighDistTwoGeometryClauses := by
  apply dimacsFormulaBounded_append
  · apply dimacsFormulaBounded_append
    · apply dimacsFormulaBounded_append <;>
        apply orderFortyNinePinnedMatchingClauses_bounded
    · apply orderFortyNinePinnedMatchingClauses_bounded
  · exact orderFortyNineConditionalEdgeUnitClauses_bounded
      3 [13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
        38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48] (fun z => z = 13)
      (by intro z hz heq; subst z; simp at hz)

theorem orderFortyNineThreeHighDistOneC2GeometryClauses_bounded :
    dimacsFormulaBounded 1176
      orderFortyNineThreeHighDistOneC2GeometryClauses := by
  apply dimacsFormulaBounded_append
  · apply dimacsFormulaBounded_append <;>
      apply orderFortyNinePinnedMatchingClauses_bounded
  · apply orderFortyNinePinnedMatchingClauses_bounded

theorem orderFortyNineThreeHighDistOneB1GeometryClauses_bounded :
    dimacsFormulaBounded 1176
      orderFortyNineThreeHighDistOneB1GeometryClauses := by
  apply dimacsFormulaBounded_append
  · apply dimacsFormulaBounded_append <;>
      apply orderFortyNinePinnedMatchingClauses_bounded
  · apply orderFortyNinePinnedMatchingClauses_bounded

theorem orderFortyNineThreeHighDistOneC1GeometryClauses_bounded :
    dimacsFormulaBounded 1176
      orderFortyNineThreeHighDistOneC1GeometryClauses := by
  apply dimacsFormulaBounded_append
  · apply dimacsFormulaBounded_append <;>
      apply orderFortyNinePinnedMatchingClauses_bounded
  · apply orderFortyNinePinnedMatchingClauses_bounded

theorem false_of_orderFortyNine_generated_h3_distTwo_scout_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighDistTwoMasks edges)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistTwoGeometryClauses)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf) : False :=
  false_of_orderFortyNine_generated_h3_scout_lrat hc
    orderFortyNineThreeHighDistTwoMasks_partitionExcluded
    orderFortyNineThreeHighDistTwoGeometryClauses_nonzero
    orderFortyNineThreeHighDistTwoGeometryClauses_bounded
    hgeometrySat proof hcheck

theorem false_of_orderFortyNine_generated_h3_distOneC2_scout_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighDistOneC2Masks edges)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistOneC2GeometryClauses)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf) : False :=
  false_of_orderFortyNine_generated_h3_scout_lrat hc
    orderFortyNineThreeHighDistOneC2Masks_partitionExcluded
    orderFortyNineThreeHighDistOneC2GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneC2GeometryClauses_bounded
    hgeometrySat proof hcheck

theorem false_of_orderFortyNine_generated_h3_distOneB1_scout_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighDistOneNoCoincidenceMasks edges)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistOneB1GeometryClauses)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf) : False :=
  false_of_orderFortyNine_generated_h3_scout_lrat hc
    orderFortyNineThreeHighDistOneNoCoincidenceMasks_partitionExcluded
    orderFortyNineThreeHighDistOneB1GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneB1GeometryClauses_bounded
    hgeometrySat proof hcheck

theorem false_of_orderFortyNine_generated_h3_distOneC1_scout_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighDistOneNoCoincidenceMasks edges)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistOneC1GeometryClauses)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf) : False :=
  false_of_orderFortyNine_generated_h3_scout_lrat hc
    orderFortyNineThreeHighDistOneNoCoincidenceMasks_partitionExcluded
    orderFortyNineThreeHighDistOneC1GeometryClauses_nonzero
    orderFortyNineThreeHighDistOneC1GeometryClauses_bounded
    hgeometrySat proof hcheck

end Erdos85
