import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfC4Completion
import Proofs.Erdos85OrderFortyNineDegreeBlocksNonzero
import Proofs.Erdos85DimacsSatBridge

/-!
# Terminal semantic-to-SAT bridge for canonical H7/T0

The semantic valuation already satisfies the exact DIMACS formula.  This
module proves, structurally, that the generator emits no zero literals and
then applies the generic DIMACS-to-`Std.Sat.CNF` transfer.
-/

namespace Erdos85

theorem seqCounterEquals_eq_core_of_interior
    (top : Nat) (vars : Array Int) (t : Nat)
    (ht0 : t ≠ 0) (htfull : t + 1 ≠ vars.size)
    (hcomp0 : vars.size - t ≠ 0)
    (hcompFull : vars.size - t + 1 ≠ vars.size) :
    seqCounterEquals top vars t = seqCounterEqualsCore top vars t := by
  simp [seqCounterEquals, seqCounterEqualsCore, seqCounterAtLeast,
    seqCounterAtLeastCore, seqCounterAtMost, ht0, htfull,
    hcomp0, hcompFull]

theorem seqCounterEquals_nonzero_of_interior
    (top : Nat) (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t : Nat) (ht0 : t ≠ 0) (htfull : t + 1 ≠ vars.size)
    (hcomp0 : vars.size - t ≠ 0)
    (hcompFull : vars.size - t + 1 ≠ vars.size) :
    ∀ clause ∈ (seqCounterEquals top vars t).clauses,
      DimacsClauseNonzero clause := by
  rw [seqCounterEquals_eq_core_of_interior top vars t
    ht0 htfull hcomp0 hcompFull]
  exact seqCounterEqualsCore_nonzero top vars hvars t

def SevenHighT0CanonicalFormulaNonzero
    (st : SevenHighT0CanonicalCnfState) : Prop :=
  ∀ clause ∈ st.clauses, DimacsClauseNonzero clause

theorem sevenHighT0CanonicalFormulaNonzero_initial :
    SevenHighT0CanonicalFormulaNonzero {} := by
  intro clause hclause
  simp at hclause

theorem sevenHighT0CanonicalDegreeStep_nonzero
    (center : Fin 42) {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (sevenHighT0CanonicalDegreeStep (center.1 + 7) st) := by
  let vars := sevenHighT0CanonicalDegreeVars center
  let target := sevenHighT0CanonicalLowDegree (center.1 + 7)
  have hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0 := by
    intro i hi
    exact (sevenHighT0CanonicalDegreeVarsRow_inputReifies
      (⊥ : SimpleGraph SevenHighT0CanonicalIndex) center).nonzero i hi
  have htarget : target = 7 ∨ target = 6 ∨ target = 5 := by
    unfold target sevenHighT0CanonicalLowDegree
    by_cases h14 : center.1 + 7 < 14
    · simp [h14]
    · by_cases h28 : center.1 + 7 < 28
      · simp [h14, h28]
      · simp [h14, h28]
  have hnew : ∀ clause ∈ (seqCounterEquals st.top vars target).clauses,
      DimacsClauseNonzero clause := by
    apply seqCounterEquals_nonzero_of_interior st.top vars hvars target
    all_goals
      have hsize : vars.size = 41 :=
        sevenHighT0CanonicalDegreeVars_size center
      rcases htarget with ht | ht | ht <;> omega
  intro clause hclause
  rw [sevenHighT0CanonicalDegreeStep,
    ← sevenHighT0CanonicalDegreeVars_eq_generator center] at hclause
  simp only [Array.mem_append] at hclause
  rcases hclause with hold | hnewClause
  · exact hst clause hold
  · exact hnew clause hnewClause

theorem sevenHighT0CanonicalDegreeNatStep_nonzero
    (center : Nat) {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (if hc : center < 42 then
        sevenHighT0CanonicalDegreeStep (center + 7) st else st) := by
  by_cases hc : center < 42
  · simpa [hc] using sevenHighT0CanonicalDegreeStep_nonzero
      ⟨center, hc⟩ hst
  · simpa [hc] using hst

theorem sevenHighT0CanonicalDegreeFold_nonzero
    (centers : List Nat) {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (centers.foldl
        (fun st center => if hc : center < 42 then
          sevenHighT0CanonicalDegreeStep (center + 7) st else st) st) := by
  induction centers generalizing st with
  | nil => exact hst
  | cons center rest ih =>
      exact ih (sevenHighT0CanonicalDegreeNatStep_nonzero center hst)

theorem sevenHighT0CanonicalDegreeFold_direct_nonzero
    (centers : List Nat) (hcenters : ∀ center ∈ centers, center < 42)
    {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (centers.foldl
        (fun st center => sevenHighT0CanonicalDegreeStep (center + 7) st) st) := by
  induction centers generalizing st with
  | nil => exact hst
  | cons center rest ih =>
      apply ih
      · intro x hx
        exact hcenters x (by simp [hx])
      · exact sevenHighT0CanonicalDegreeStep_nonzero
          ⟨center, hcenters center (by simp)⟩ hst

theorem sevenHighT0CanonicalDegreeState_nonzero :
    SevenHighT0CanonicalFormulaNonzero sevenHighT0CanonicalDegreeState := by
  rw [sevenHighT0CanonicalDegreeState, sevenHighT0CanonicalLows,
    List.foldl_map]
  exact sevenHighT0CanonicalDegreeFold_direct_nonzero (List.range 42)
    (by simp) sevenHighT0CanonicalFormulaNonzero_initial

theorem sevenHighT0CanonicalC4Clause_nonzero
    (statuses : List SevenHighT0CanonicalEdgeStatus)
    (hpositive : ∀ status ∈ statuses, ∀ id,
      status = .variable id → 0 < id) :
    DimacsClauseNonzero
      (statuses.filterMap sevenHighT0CanonicalC4Literal) := by
  intro lit hlit
  rw [List.mem_filterMap] at hlit
  obtain ⟨status, hstatus, hliteral⟩ := hlit
  cases status with
  | fixedFalse => simp [sevenHighT0CanonicalC4Literal] at hliteral
  | fixedTrue => simp [sevenHighT0CanonicalC4Literal] at hliteral
  | «variable» id =>
      simp only [sevenHighT0CanonicalC4Literal, Option.some.injEq] at hliteral
      subst lit
      have hid := hpositive (.variable id) hstatus id rfl
      simp
      omega

theorem sevenHighT0CanonicalC4Step_nonzero
    (endpoints witnesses : Nat × Nat)
    {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (sevenHighT0CanonicalC4Step endpoints witnesses st) := by
  let statuses :=
    [sevenHighT0CanonicalEdgeStatus endpoints.1 witnesses.1,
     sevenHighT0CanonicalEdgeStatus endpoints.2 witnesses.1,
     sevenHighT0CanonicalEdgeStatus endpoints.1 witnesses.2,
     sevenHighT0CanonicalEdgeStatus endpoints.2 witnesses.2]
  by_cases hfalse : statuses.contains .fixedFalse = true
  · change SevenHighT0CanonicalFormulaNonzero
      (if statuses.contains .fixedFalse then st else _)
    have hm : .fixedFalse ∈ statuses := by
      simpa only [← List.contains_iff_mem] using hfalse
    simp [hm, hst]
  · have hclause : DimacsClauseNonzero
        (statuses.filterMap sevenHighT0CanonicalC4Literal) := by
      apply sevenHighT0CanonicalC4Clause_nonzero statuses
      intro status hstatus id hid
      simp [statuses] at hstatus
      rcases hstatus with hstatus | hstatus | hstatus | hstatus
      · exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id
          (hstatus.symm.trans hid)
      · exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id
          (hstatus.symm.trans hid)
      · exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id
          (hstatus.symm.trans hid)
      · exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id
          (hstatus.symm.trans hid)
    intro clause hclauseMem
    simp only [sevenHighT0CanonicalC4Step, statuses, hfalse,
      Bool.false_eq_true, ↓reduceIte, Array.mem_push] at hclauseMem
    rcases hclauseMem with hold | rfl
    · exact hst clause hold
    · exact hclause

theorem sevenHighT0CanonicalC4WitnessFold_nonzero
    (pairs : List (Nat × Nat)) (endpoints : Nat × Nat)
    {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (pairs.foldl
        (fun st witnesses =>
          sevenHighT0CanonicalC4Step endpoints witnesses st) st) := by
  induction pairs generalizing st with
  | nil => exact hst
  | cons witnesses rest ih =>
      exact ih (sevenHighT0CanonicalC4Step_nonzero endpoints witnesses hst)

theorem sevenHighT0CanonicalC4EndpointStep_nonzero
    (endpoints : Nat × Nat) {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (sevenHighT0CanonicalC4EndpointStep endpoints st) := by
  unfold sevenHighT0CanonicalC4EndpointStep
  exact sevenHighT0CanonicalC4WitnessFold_nonzero _ endpoints hst

theorem sevenHighT0CanonicalC4EndpointFold_nonzero
    (pairs : List (Nat × Nat)) {st : SevenHighT0CanonicalCnfState}
    (hst : SevenHighT0CanonicalFormulaNonzero st) :
    SevenHighT0CanonicalFormulaNonzero
      (pairs.foldl
        (fun st endpoints =>
          sevenHighT0CanonicalC4EndpointStep endpoints st) st) := by
  induction pairs generalizing st with
  | nil => exact hst
  | cons endpoints rest ih =>
      exact ih (sevenHighT0CanonicalC4EndpointStep_nonzero endpoints hst)

theorem sevenHighT0CanonicalFinalState_nonzero :
    SevenHighT0CanonicalFormulaNonzero sevenHighT0CanonicalFinalState := by
  rw [sevenHighT0CanonicalFinalState]
  exact sevenHighT0CanonicalC4EndpointFold_nonzero _
    sevenHighT0CanonicalDegreeState_nonzero

/-- Every canonical completion semantics gives the concrete auxiliary-aware
DIMACS valuation required by the empty-cube semantic-cover assembler. -/
theorem sevenHighT0CanonicalBaseSat
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    ∃ val : DimacsValuation,
      orderFortyNineSevenHighT0CanonicalSatCnf.Sat
          (satAssignmentOfDimacs val) ∧
        ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id := by
  let val := (sevenHighT0CanonicalDegreeStateVal H).2
  have degreeSound :=
    sevenHighT0CanonicalDegreeStateVal_semanticSound H semantics
  refine ⟨val, ?_, degreeSound.edge_agree⟩
  change (show Std.Sat.CNF Nat from
    ⟨dimacsFormulaToSatClauses sevenHighT0CanonicalFinalState.clauses⟩).Sat
      (satAssignmentOfDimacs val)
  exact satCnf_of_dimacsFormulaSatisfied
    sevenHighT0CanonicalFinalState_nonzero
    (sevenHighT0CanonicalFinalState_satisfied H semantics)

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalDegreeState_nonzero
#print axioms Erdos85.sevenHighT0CanonicalFinalState_nonzero
#print axioms Erdos85.sevenHighT0CanonicalBaseSat
