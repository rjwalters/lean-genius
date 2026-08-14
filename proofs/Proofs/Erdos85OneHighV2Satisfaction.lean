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

noncomputable def oneHighFamilyV2SaverStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x w : Nat) (accst : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (ss, acc) := accst
  let (s, acc) := oneHighFamilyAtomIdVal R (.saver x w) acc
  let (exw, acc) := oneHighFamilyEdgeIdVal R x w acc
  let (mw, acc) := oneHighFamilyAtomIdVal R
    (.miss w (x / 5 ^^^ 1)) acc
  let acc := (oneHighFamilyEmitVal [-(s : Int), (exw : Int)] acc).2
  let acc := (oneHighFamilyEmitVal [-(s : Int), (mw : Int)] acc).2
  let acc := (oneHighFamilyEmitVal
    [(s : Int), -(exw : Int), -(mw : Int)] acc).2
  (ss.push (s : Int), acc)

theorem oneHighFamilyV2SaverStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x w : Nat) (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyV2SaverStepVal R x w input).2.1 =
      (oneHighFamilyV2SaverStep x w (input.1, input.2.1)).2 := by
  rcases input with ⟨ss, st, val⟩
  generalize hv₁ : oneHighFamilyAtomIdVal R (.saver x w) (st, val) = out₁
  rcases out₁ with ⟨s, acc₁⟩
  have hid₁ := oneHighFamilyAtomIdVal_id R (.saver x w) st val
  have hst₁ := oneHighFamilyAtomIdVal_state R (.saver x w) st val
  rw [hv₁] at hid₁ hst₁
  generalize hv₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  have hid₂ := oneHighFamilyAtomIdVal_id R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2
  have hst₂ := oneHighFamilyAtomIdVal_state R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2
  rw [hv₂] at hid₂ hst₂
  generalize hv₃ : oneHighFamilyAtomIdVal R
    (.miss w (x / 5 ^^^ 1)) acc₂ = out₃
  rcases out₃ with ⟨mw, acc₃⟩
  have hid₃ := oneHighFamilyAtomIdVal_id R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2
  have hst₃ := oneHighFamilyAtomIdVal_state R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2
  rw [hv₃] at hid₃ hst₃
  have hout₁ : oneHighFamilyAtomId (.saver x w) st = (s, acc₁.1) :=
    Prod.ext hid₁.symm hst₁.symm
  have hout₂ : oneHighFamilyEdgeId x w acc₁.1 = (exw, acc₂.1) :=
    Prod.ext hid₂.symm hst₂.symm
  have hout₃ : oneHighFamilyAtomId (.miss w (x / 5 ^^^ 1)) acc₂.1 =
      (mw, acc₃.1) := Prod.ext hid₃.symm hst₃.symm
  simp [oneHighFamilyV2SaverStepVal, oneHighFamilyV2SaverStep,
    oneHighFamilyEdgeIdVal, hv₁, hv₂, hv₃,
    hout₁, hout₂, hout₃, oneHighFamilyEmitVal]

theorem oneHighFamilyV2SaverStepVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x w : Nat) (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyV2SaverStepVal R x w input
    let raw := oneHighFamilyV2SaverStep x w (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  constructor
  · rcases input with ⟨ss, st, val⟩
    generalize hv : oneHighFamilyAtomIdVal R (.saver x w) (st, val) = outV
    rcases outV with ⟨s, acc₁⟩
    generalize hg : oneHighFamilyAtomId (.saver x w) st = outG
    rcases outG with ⟨sg, st₁⟩
    have hid := oneHighFamilyAtomIdVal_id R (.saver x w) st val
    rw [hv, hg] at hid
    dsimp at hid
    subst sg
    generalize hv₂ : oneHighFamilyAtomIdVal R
      (.edge (min x w) (max x w)) acc₁ = outV₂
    rcases outV₂ with ⟨exw, acc₂⟩
    generalize hv₃ : oneHighFamilyAtomIdVal R
      (.miss w (x / 5 ^^^ 1)) acc₂ = outV₃
    rcases outV₃ with ⟨mw, acc₃⟩
    generalize hg₂ : oneHighFamilyEdgeId x w st₁ = outG₂
    rcases outG₂ with ⟨exwg, st₂⟩
    generalize hg₃ : oneHighFamilyAtomId
      (.miss w (x / 5 ^^^ 1)) st₂ = outG₃
    rcases outG₃ with ⟨mwg, st₃⟩
    simp [oneHighFamilyV2SaverStepVal, oneHighFamilyV2SaverStep,
      oneHighFamilyEdgeIdVal, hv, hg, hv₂, hv₃, hg₂, hg₃]
  · exact oneHighFamilyV2SaverStepVal_state R x w input

theorem oneHighFamilyV2CollectSaversVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Nat) (ws : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := ws.foldl
      (fun input w => oneHighFamilyV2SaverStepVal R x w input) input
    let raw := ws.foldl
      (fun input w => oneHighFamilyV2SaverStep x w input)
      (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction ws generalizing input with
  | nil => simp
  | cons w ws ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyV2SaverStepVal_projection R x w input
      have hi := ih (oneHighFamilyV2SaverStepVal R x w input)
      rcases hp with ⟨hvars, hst⟩
      simpa [hvars, hst] using hi

theorem oneHighFamilyV2SaverStepVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x w : Nat) {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyV2SaverStepVal R x w input).2.1.ids := by
  rcases input with ⟨ss, acc⟩
  simp only [oneHighFamilyV2SaverStepVal, oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R (.saver x w) acc = out₁
  rcases out₁ with ⟨s, acc₁⟩
  have hm₁ := oneHighFamilyAtomIdVal_old_mem R
    (.saver x w) acc.1 acc.2 hmem
  rw [h₁] at hm₁
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  have hm₂ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hm₁
  rw [h₂] at hm₂
  generalize h₃ : oneHighFamilyAtomIdVal R
    (.miss w (x / 5 ^^^ 1)) acc₂ = out₃
  rcases out₃ with ⟨mw, acc₃⟩
  have hm₃ := oneHighFamilyAtomIdVal_old_mem R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2 hm₂
  rw [h₃] at hm₃
  simp only [h₁, h₂, h₃]
  exact hm₃

noncomputable def oneHighFamilyCollectedSaversMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x : Nat} {ws : List Nat} {w : Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedAtomsMatch
      (ws.map fun w => OneHighFamilyAtom.saver x w) input) :
    OneHighFamilyCollectedAtomsMatch
      ((ws ++ [w]).map fun w => OneHighFamilyAtom.saver x w)
      (oneHighFamilyV2SaverStepVal R x w input) := by
  rcases input with ⟨ss, acc⟩
  simp only [oneHighFamilyV2SaverStepVal, oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R (.saver x w) acc = out₁
  rcases out₁ with ⟨s, acc₁⟩
  have hnew₁ := (oneHighFamilyAtomIdVal_result R
    (.saver x w) acc.1 acc.2).1
  rw [h₁] at hnew₁
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  have hnew₂ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hnew₁
  rw [h₂] at hnew₂
  generalize h₃ : oneHighFamilyAtomIdVal R
    (.miss w (x / 5 ^^^ 1)) acc₂ = out₃
  rcases out₃ with ⟨mw, acc₃⟩
  have hnew₃ := oneHighFamilyAtomIdVal_old_mem R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2 hnew₂
  rw [h₃] at hnew₃
  refine ⟨h.ids ++ [s], ?_, ?_⟩
  · change (ss.push (s : Int)).toList = _
    rw [Array.toList_push, h.vars_eq]
    simp
  · rw [List.map_append]
    simp only [List.map_cons, List.map_nil]
    simp only [h₂, h₃, oneHighFamilyEmitVal]
    change List.Forall₂ (fun atom id => (atom, id) ∈ acc₃.1.ids)
      ((ws.map fun w => OneHighFamilyAtom.saver x w) ++
        [OneHighFamilyAtom.saver x w]) (h.ids ++ [s])
    have hold : List.Forall₂ (fun atom id =>
        (atom, id) ∈ acc₃.1.ids)
        (ws.map fun w => OneHighFamilyAtom.saver x w) h.ids := by
      apply h.aligned.imp
      intro atom id hm
      have hm₁ := oneHighFamilyAtomIdVal_old_mem R
        (.saver x w) acc.1 acc.2 hm
      rw [h₁] at hm₁
      have hm₂ := oneHighFamilyAtomIdVal_old_mem R
        (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hm₁
      rw [h₂] at hm₂
      have hm₃ := oneHighFamilyAtomIdVal_old_mem R
        (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2 hm₂
      rw [h₃] at hm₃
      exact hm₃
    exact listForall₂_append_singleton hold hnew₃

noncomputable def oneHighFamilyCollectSaversVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Nat) (ws : List Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedAtomsMatch
      (ws.map fun w => OneHighFamilyAtom.saver x w)
      (ws.foldl (fun input w => oneHighFamilyV2SaverStepVal R x w input)
        (#[], acc)) := by
  induction ws using List.reverseRecOn with
  | nil => exact oneHighFamilyCollectedAtomsMatch_empty acc
  | append_singleton ws w ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact oneHighFamilyCollectedSaversMatch_push R ih

theorem oneHighFamilyV2SaverStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x w : Nat} (hx : x < 40) (hw : w < 40)
    (hb : (x / 5 ^^^ 1) < 8)
    {ss : Array Int} {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2SaverStepVal R x w (ss, acc)).2 := by
  simp only [oneHighFamilyV2SaverStepVal, oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R (.saver x w) acc = out₁
  rcases out₁ with ⟨s, acc₁⟩
  have hs₁ := oneHighFamilyAtomIdVal_semanticSound R hacc (.saver x w)
  rw [h₁] at hs₁
  have hr₁ := oneHighFamilyAtomIdVal_result R (.saver x w) acc.1 acc.2
  rw [h₁] at hr₁
  dsimp at hr₁
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  have hs₂ := oneHighFamilyAtomIdVal_semanticSound R hs₁
    (.edge (min x w) (max x w))
  rw [h₂] at hs₂
  have hr₂ := oneHighFamilyAtomIdVal_result R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2
  rw [h₂] at hr₂
  dsimp at hr₂
  generalize h₃ : oneHighFamilyAtomIdVal R
    (.miss w (x / 5 ^^^ 1)) acc₂ = out₃
  rcases out₃ with ⟨mw, acc₃⟩
  have hs₃ := oneHighFamilyAtomIdVal_semanticSound R hs₂
    (.miss w (x / 5 ^^^ 1))
  rw [h₃] at hs₃
  have hr₃ := oneHighFamilyAtomIdVal_result R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2
  rw [h₃] at hr₃
  dsimp at hr₃
  have hs₂mem := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hr₁.1
  rw [h₂] at hs₂mem
  have hs₃mem := oneHighFamilyAtomIdVal_old_mem R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2 hs₂mem
  rw [h₃] at hs₃mem
  have he₃mem := oneHighFamilyAtomIdVal_old_mem R
    (.miss w (x / 5 ^^^ 1)) acc₂.1 acc₂.2 hr₂.1
  rw [h₃] at he₃mem
  have hsVal : acc₃.2 s =
      (decide (R.Adj (⟨x, hx⟩ : Fin 40) ⟨w, hw⟩) &&
        @decide (oneHighFamilyMissesBlock R (⟨w, hw⟩ : Fin 40)
          (⟨x / 5 ^^^ 1, hb⟩ : Fin 8)) (Classical.propDecidable _)) := by
    rw [hs₃.named (.saver x w) s hs₃mem]
    simp [oneHighFamilyAtomValue, hx, hw, hb]
  have heVal : acc₃.2 exw =
      decide (R.Adj (⟨x, hx⟩ : Fin 40) ⟨w, hw⟩) :=
    (hs₃.named _ exw he₃mem).trans (oneHighFamilyAtomValue_edge R hx hw)
  have hmVal : acc₃.2 mw =
      @decide (oneHighFamilyMissesBlock R (⟨w, hw⟩ : Fin 40)
        (⟨x / 5 ^^^ 1, hb⟩ : Fin 8)) (Classical.propDecidable _) := by
    rw [hr₃.2]
    simp [oneHighFamilyAtomValue, hw, hb]
  have hse : acc₃.2 s = true → acc₃.2 exw = true := by
    rw [hsVal, heVal]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  have hsm : acc₃.2 s = true → acc₃.2 mw = true := by
    rw [hsVal, hmVal]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  have hems : acc₃.2 exw = true → acc₃.2 mw = true → acc₃.2 s = true := by
    rw [hsVal, heVal, hmVal]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  let acc₄ := (oneHighFamilyEmitVal [-(s : Int), (exw : Int)] acc₃).2
  have hs₄ : OneHighFamilySemanticSound R acc₄ := by
    apply oneHighFamilyEmitVal_semanticSound R hs₃
    · exact dimacsClauseSatisfied_negative_positive
        (hs₃.ids.id_bounds _ he₃mem).1 hse
    · exact dimacsClauseBounded_negative_positive
        (hs₃.ids.id_bounds _ hs₃mem).2
        (hs₃.ids.id_bounds _ he₃mem).2
  let acc₅ := (oneHighFamilyEmitVal [-(s : Int), (mw : Int)] acc₄).2
  have hs₅ : OneHighFamilySemanticSound R acc₅ := by
    apply oneHighFamilyEmitVal_semanticSound R hs₄
    · simpa [acc₄, oneHighFamilyEmitVal] using
        dimacsClauseSatisfied_negative_positive
          (hs₃.ids.id_bounds _ hr₃.1).1 hsm
    · exact dimacsClauseBounded_negative_positive
        (hs₄.ids.id_bounds _ hs₃mem).2
        (hs₄.ids.id_bounds _ hr₃.1).2
  simp only [h₂, h₃]
  apply oneHighFamilyEmitVal_semanticSound R hs₅
  · simpa [acc₄, acc₅, oneHighFamilyEmitVal] using
      dimacsClauseSatisfied_positive_negative_pair
        (hs₃.ids.id_bounds _ hs₃mem).1 hems
  · exact dimacsClauseBounded_positive_negative_pair
      (hs₅.ids.id_bounds _ hs₃mem).2
      (hs₅.ids.id_bounds _ he₃mem).2
      (hs₅.ids.id_bounds _ hr₃.1).2

theorem oneHighFamilyV2CollectSaversVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x : Nat} (hx : x < 40) {ws : List Nat}
    (hws : ∀ w ∈ ws, w < 40) (hb : (x / 5 ^^^ 1) < 8)
    {ss : Array Int} {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (ws.foldl (fun input w =>
        oneHighFamilyV2SaverStepVal R x w input) (ss, acc)).2 := by
  induction ws generalizing ss acc with
  | nil => exact hacc
  | cons w ws ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro z hz
        exact hws z (List.mem_cons_of_mem w hz)
      · exact oneHighFamilyV2SaverStepVal_semanticSound R hx
          (hws w (by simp)) hb (ss := ss) hacc

end Erdos85
