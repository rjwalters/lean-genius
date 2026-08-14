import Proofs.Erdos85OneHighV2Cnf

/-!
# Semantic replay of the exact fleet-v2 generator

The replay is factored at the same stage boundaries as the worker.  Graph
ledger facts are explicit inputs, so their transport from the original
order-49 graph can be audited independently from Tseitin/counter mechanics.
-/

namespace Erdos85

structure OneHighFamilyV2F1Ledger
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] : Prop where
  table_symm : ∀ c j,
    oneHighFamilyGraphTable R a c j = oneHighFamilyGraphTable R a j c

noncomputable def oneHighFamilyV2UpperTableClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal oneHighFamilyTablePairs
    (oneHighFamilyTablePairStepVal R a (oneHighFamilyGraphTable R a))
    (oneHighFamilyMissDefinitionClausesVal R a val)

theorem oneHighFamilyV2UpperTableClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2UpperTableClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound R _ _
    (oneHighFamilyMissDefinitionClausesVal_semanticSound a R hc val)
  intro pair acc hacc
  exact oneHighFamilyTablePairStepVal_semanticSound R a pair hacc

theorem oneHighFamilyV2UpperTableClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2UpperTableClausesVal R a val).1 =
      oneHighFamilyV2UpperTableClauses a
        (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2UpperTableClausesVal
    oneHighFamilyV2UpperTableClauses
  calc
    _ = oneHighFamilyRunList oneHighFamilyTablePairs
        (oneHighFamilyTablePairStep a (oneHighFamilyGraphTable R a))
        (oneHighFamilyMissDefinitionClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyTablePairStepVal_state R a
          (oneHighFamilyGraphTable R a) pair acc)
    _ = _ := by rw [oneHighFamilyMissDefinitionClausesVal_state]

noncomputable def oneHighFamilyV2LexClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 8)
    (oneHighFamilyLexBlockStepVal R a)
    (oneHighFamilyV2UpperTableClausesVal R a val)

theorem oneHighFamilyV2LexClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (oneHighFamilyV2LexClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2UpperTableClausesVal_semanticSound R a hc val)
  intro c hcMem acc hacc
  exact oneHighFamilyLexBlockStepVal_semanticSound a R hc
    (List.mem_range.mp hcMem) hacc

theorem oneHighFamilyV2LexClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2LexClausesVal R a val).1 =
      oneHighFamilyV2LexClauses a (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2LexClausesVal oneHighFamilyV2LexClauses
  calc
    _ = oneHighFamilyRunList (List.range 8)
        (oneHighFamilyLexBlockStep a)
        (oneHighFamilyV2UpperTableClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun c acc => oneHighFamilyLexBlockStepVal_state R a c acc)
    _ = _ := by rw [oneHighFamilyV2UpperTableClausesVal_state]

noncomputable def oneHighFamilyV2LowerTablePairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let atoms := oneHighFamilyTableMissAtoms a pair.1 pair.2
  let input := oneHighFamilyCollectAtomsVal R atoms acc
  oneHighFamilyEqualsBlockVal input.1 (oneHighFamilyInputAccumRow input)
    (table pair.2 pair.1) input.2

theorem oneHighFamilyV2LowerTablePairStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (ledger : OneHighFamilyV2F1Ledger a R)
    (pair : Nat × Nat) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2LowerTablePairStepVal R a
        (oneHighFamilyGraphTable R a) pair acc) := by
  let atoms := oneHighFamilyTableMissAtoms a pair.1 pair.2
  let input := oneHighFamilyCollectAtomsVal R atoms acc
  have hsInput : OneHighFamilyInputAccumSound R input := by
    exact oneHighFamilyCollectAtomsVal_sound R atoms
      (oneHighFamilyInputAccumSound_empty R hacc)
  apply oneHighFamilyEqualsBlockVal_semanticSound R hsInput.semantic
  · exact oneHighFamilyInputAccum_reifies R hsInput
  · calc
      seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
          (List.ofFn (oneHighFamilyInputAccumRow input)).count true :=
        seqPrefixTrue_oneHighFamilyLiteralRow_eq_countP input.2.2 input.1
      _ = (atoms.map (oneHighFamilyAtomValue R)).count true := by
        rw [oneHighFamilyCollectedAtoms_values R
          (oneHighFamilyCollectAtomsVal_match R atoms acc) hsInput.semantic]
      _ = oneHighFamilyGraphTable R a pair.1 pair.2 := rfl
      _ = oneHighFamilyGraphTable R a pair.2 pair.1 :=
        ledger.table_symm pair.1 pair.2

theorem oneHighFamilyV2LowerTablePairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyV2LowerTablePairStepVal R a table pair acc).1 =
      oneHighFamilyV2LowerTablePairStep a table pair acc.1 := by
  unfold oneHighFamilyV2LowerTablePairStepVal
    oneHighFamilyV2LowerTablePairStep
  let atoms := oneHighFamilyTableMissAtoms a pair.1 pair.2
  let input := oneHighFamilyCollectAtomsVal R atoms acc
  have hp := oneHighFamilyCollectAtomsVal_projection R atoms acc
  change (oneHighFamilyEqualsBlockVal input.1
      (oneHighFamilyInputAccumRow input) (table pair.2 pair.1) input.2).1 = _
  rw [oneHighFamilyEqualsBlockVal_state]
  rcases hp with ⟨hvars, hstate⟩
  simp only [oneHighFamilyTableMissVars, atoms] at hvars hstate ⊢
  rw [hvars, hstate]

noncomputable def oneHighFamilyV2F1ClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal oneHighFamilyV2LowerTablePairs
    (oneHighFamilyV2LowerTablePairStepVal R a
      (oneHighFamilyGraphTable R a))
    (oneHighFamilyV2LexClausesVal R a val)

theorem oneHighFamilyV2F1ClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (ledger : OneHighFamilyV2F1Ledger a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (oneHighFamilyV2F1ClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound R _ _
    (oneHighFamilyV2LexClausesVal_semanticSound R a hc val)
  intro pair acc hacc
  exact oneHighFamilyV2LowerTablePairStepVal_semanticSound
    R a ledger pair hacc

theorem oneHighFamilyV2F1ClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2F1ClausesVal R a val).1 =
      oneHighFamilyV2F1Clauses a (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2F1ClausesVal oneHighFamilyV2F1Clauses
  calc
    _ = oneHighFamilyRunList oneHighFamilyV2LowerTablePairs
        (oneHighFamilyV2LowerTablePairStep a
          (oneHighFamilyGraphTable R a))
        (oneHighFamilyV2LexClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyV2LowerTablePairStepVal_state R a
          (oneHighFamilyGraphTable R a) pair acc)
    _ = _ := by rw [oneHighFamilyV2LexClausesVal_state]

noncomputable def oneHighFamilyV2PairedCommonBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let bi := 2 * pair
  let bj := bi + 1
  (oneHighFamilyCollectCommonsVal R bi bj acc).2

theorem oneHighFamilyV2PairedCommonBlockStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    {pair : Nat} (hpair : pair < 4) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2PairedCommonBlockStepVal R pair acc) := by
  exact oneHighFamilyCollectCommonsVal_semanticSound
    a R hc pair hpair acc hacc

theorem oneHighFamilyV2PairedCommonBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyV2PairedCommonBlockStepVal R pair acc).1 =
      oneHighFamilyV2PairedCommonBlockStep pair acc.1 := by
  unfold oneHighFamilyV2PairedCommonBlockStepVal
    oneHighFamilyV2PairedCommonBlockStep
  have hp := oneHighFamilyCollectCommonsVal_projection R
    (2 * pair) (2 * pair + 1) acc
  exact hp.2

noncomputable def oneHighFamilyV2PairedCommonClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 4)
    (oneHighFamilyV2PairedCommonBlockStepVal R)
    (oneHighFamilyV2F1ClausesVal R a val)

theorem oneHighFamilyV2PairedCommonClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (ledger : OneHighFamilyV2F1Ledger a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2PairedCommonClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2F1ClausesVal_semanticSound R a hc ledger val)
  intro pair hp acc hacc
  exact oneHighFamilyV2PairedCommonBlockStepVal_semanticSound R a hc
    (List.mem_range.mp hp) hacc

theorem oneHighFamilyV2PairedCommonClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2PairedCommonClausesVal R a val).1 =
      oneHighFamilyV2PairedCommonClauses a
        (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2PairedCommonClausesVal
    oneHighFamilyV2PairedCommonClauses
  calc
    _ = oneHighFamilyRunList (List.range 4)
        oneHighFamilyV2PairedCommonBlockStep
        (oneHighFamilyV2F1ClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyV2PairedCommonBlockStepVal_state
          R pair acc)
    _ = _ := by rw [oneHighFamilyV2F1ClausesVal_state]

end Erdos85
