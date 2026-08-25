import Proofs.Erdos85OneHighRefinementPinnedCnf

/-! # Satisfaction interface for refinement-pinned one-high CNFs -/

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000

/-- Semantic payload needed by the unit-pin layer.  Stating it through the
already checked named-atom interpretation cleanly separates CNF valuation
soundness from the later graph theorem identifying canonical slot labels. -/
def OneHighRefinementPinSemantics
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (refinement : List (List OneHighLabelPair)) : Prop :=
  ∀ source edge, edge < (refinement.getD source []).length →
    let pair := (refinement.getD source []).getD edge (0, 0)
    oneHighFamilyAtomValue R
        (.miss (5 * source + 2 * edge) pair.1.val) = true ∧
      oneHighFamilyAtomValue R
        (.miss (5 * source + 2 * edge + 1) pair.2.val) = true

/-- Valuation-producing counterpart of one pinned canonical edge. -/
def oneHighFamilyRefinementPinEdgeStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (refinement : List (List OneHighLabelPair)) (source edge : Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let pair := (refinement.getD source []).getD edge (0, 0)
  let leftVertex := 5 * source + 2 * edge
  let rightVertex := leftVertex + 1
  let (leftId, acc) := oneHighFamilyAtomIdVal R
    (.miss leftVertex pair.1.val) acc
  let acc := (oneHighFamilyEmitVal [(leftId : Int)] acc).2
  let (rightId, acc) := oneHighFamilyAtomIdVal R
    (.miss rightVertex pair.2.val) acc
  (oneHighFamilyEmitVal [(rightId : Int)] acc).2

theorem oneHighFamilyRefinementPinEdgeStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (refinement : List (List OneHighLabelPair)) (source edge : Nat)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyRefinementPinEdgeStepVal R refinement source edge acc).1 =
      oneHighFamilyRefinementPinEdgeStep refinement source edge acc.1 := by
  simp only [oneHighFamilyRefinementPinEdgeStepVal,
    oneHighFamilyRefinementPinEdgeStep, oneHighFamilyAtomIdVal,
    oneHighFamilyEmitVal]
  generalize hleft : oneHighFamilyAtomId
    (.miss (5 * source + 2 * edge)
      ((refinement.getD source []).getD edge (0, 0)).1.val) acc.1 = left
  rcases left with ⟨leftId, st₁⟩
  generalize hright : oneHighFamilyAtomId
    (.miss (5 * source + 2 * edge + 1)
      ((refinement.getD source []).getD edge (0, 0)).2.val)
      (oneHighFamilyEmit [(leftId : Int)] st₁).2 = right
  rcases right with ⟨rightId, st₂⟩
  rfl

private theorem oneHighFamilyPositiveMissUnitVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (w b : Nat)
    (hvalue : oneHighFamilyAtomValue R (.miss w b) = true) :
    OneHighFamilySemanticSound R
      ((fun acc =>
        let (id, acc) := oneHighFamilyAtomIdVal R (.miss w b) acc
        (oneHighFamilyEmitVal [(id : Int)] acc).2) (st, val)) := by
  generalize hout : oneHighFamilyAtomIdVal R (.miss w b) (st, val) = out
  rcases out with ⟨id, acc⟩
  have hs := oneHighFamilyAtomIdVal_semanticSound R h (.miss w b)
  rw [hout] at hs
  have hr := oneHighFamilyAtomIdVal_result R (.miss w b) st val
  rw [hout] at hr
  have hbounds := hs.ids.id_bounds _ hr.1
  have hval : acc.2 id = true := hr.2.trans hvalue
  dsimp only
  rw [hout]
  exact oneHighFamilyEmitVal_semanticSound R hs [(id : Int)]
    (dimacsClauseSatisfied_singleton_positive hbounds.1 hval)
    (dimacsClauseBounded_singleton_positive hbounds.2)

theorem oneHighFamilyRefinementPinEdgeStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {refinement : List (List OneHighLabelPair)} {source edge : Nat}
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hpins : OneHighRefinementPinSemantics R refinement)
    (hedge : edge < (refinement.getD source []).length) :
    OneHighFamilySemanticSound R
      (oneHighFamilyRefinementPinEdgeStepVal
        R refinement source edge acc) := by
  have hp := hpins source edge hedge
  simp only [OneHighRefinementPinSemantics] at hpins
  simp only [oneHighFamilyRefinementPinEdgeStepVal]
  exact oneHighFamilyPositiveMissUnitVal_semanticSound R
    (oneHighFamilyPositiveMissUnitVal_semanticSound R h _ _ hp.1)
    _ _ hp.2

/-- Valuation-producing fold over one pinned source row. -/
def oneHighFamilyRefinementPinRowStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (refinement : List (List OneHighLabelPair)) (source : Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range (refinement.getD source []).length)
    (oneHighFamilyRefinementPinEdgeStepVal R refinement source) acc

theorem oneHighFamilyRefinementPinRowStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {refinement : List (List OneHighLabelPair)} {source : Nat}
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hpins : OneHighRefinementPinSemantics R refinement) :
    OneHighFamilySemanticSound R
      (oneHighFamilyRefinementPinRowStepVal R refinement source acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro edge hedge acc' hs
  exact oneHighFamilyRefinementPinEdgeStepVal_semanticSound R hs hpins
    (List.mem_range.mp hedge)

theorem oneHighFamilyRefinementPinRowStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (refinement : List (List OneHighLabelPair)) (source : Nat)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyRefinementPinRowStepVal R refinement source acc).1 =
      oneHighFamilyRefinementPinRowStep refinement source acc.1 := by
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun edge acc' =>
      oneHighFamilyRefinementPinEdgeStepVal_state
        R refinement source edge acc')

/-- Complete semantic runner for the lex-prefix plus refinement units. -/
def oneHighFamilyRefinementClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (refinement : List (List OneHighLabelPair))
    (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 8)
    (oneHighFamilyRefinementPinRowStepVal R refinement)
    (oneHighFamilyLexClausesVal R profile val)

theorem oneHighFamilyRefinementClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (refinement : List (List OneHighLabelPair))
    (hc : OneHighPureFamilyCnfConstraints profile R)
    (hpins : OneHighRefinementPinSemantics R refinement)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyRefinementClausesVal R profile refinement val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyLexClausesVal_semanticSound profile R hc val)
  intro source _ acc hs
  exact oneHighFamilyRefinementPinRowStepVal_semanticSound R hs hpins

theorem oneHighFamilyRefinementClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (refinement : List (List OneHighLabelPair))
    (val : DimacsValuation) :
    (oneHighFamilyRefinementClausesVal R profile refinement val).1 =
      oneHighFamilyRefinementClauses profile refinement := by
  unfold oneHighFamilyRefinementClausesVal oneHighFamilyRefinementClauses
  calc
    _ = oneHighFamilyRunList (List.range 8)
        (oneHighFamilyRefinementPinRowStep refinement)
        (oneHighFamilyLexClausesVal R profile val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun source acc =>
          oneHighFamilyRefinementPinRowStepVal_state
            R refinement source acc)
    _ = _ := by rw [oneHighFamilyLexClausesVal_state]

end


end Erdos85

#print axioms Erdos85.oneHighFamilyRefinementPinEdgeStepVal_semanticSound
