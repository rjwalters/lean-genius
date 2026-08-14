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
  table_symm : ∀ (c j : Fin 8), j ≠ c →
    j ≠ oneHighStandardMate c →
    oneHighFamilyGraphTable R a c.val j.val =
      oneHighFamilyGraphTable R a j.val c.val

theorem oneHighFamilyV2LowerTablePairs_mem_bounds
    {pair : Nat × Nat} (h : pair ∈ oneHighFamilyV2LowerTablePairs) :
    pair.1 < 8 ∧ pair.2 < 8 ∧ pair.2 ≠ pair.1 ∧
      pair.2 ≠ (pair.1 ^^^ 1) := by
  native_decide +revert

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
    (hpair : pair ∈ oneHighFamilyV2LowerTablePairs)
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
        ledger.table_symm ⟨pair.1,
          (oneHighFamilyV2LowerTablePairs_mem_bounds hpair).1⟩
          ⟨pair.2, (oneHighFamilyV2LowerTablePairs_mem_bounds hpair).2.1⟩
          (by
            intro h
            exact (oneHighFamilyV2LowerTablePairs_mem_bounds hpair).2.2.1
              (congrArg Fin.val h))
          (by
            intro h
            apply (oneHighFamilyV2LowerTablePairs_mem_bounds hpair).2.2.2
            simpa [oneHighStandardMate_val_eq_xor] using congrArg Fin.val h)

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
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2LexClausesVal_semanticSound R a hc val)
  intro pair hpair acc hacc
  exact oneHighFamilyV2LowerTablePairStepVal_semanticSound
    R a ledger pair hpair hacc

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

def oneHighFamilyV2PairedCommonAtoms (x : Nat) :
    List OneHighFamilyAtom :=
  (oneHighFamilyBlockVertices (x / 5 ^^^ 1)).map fun z =>
    .common (min x z) (max x z)

def oneHighFamilyV2SaverAtoms (a x : Nat) :
    List OneHighFamilyAtom :=
  (oneHighFamilyV2SaverVertices a x).map fun w => .saver x w

theorem oneHighFamilyCollectAtomsFoldVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat} (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (atoms.foldl (fun input atom =>
      oneHighFamilyCollectAtomVal R atom input) input).2.1.ids := by
  induction atoms generalizing input with
  | nil => exact hmem
  | cons atom atoms ih =>
    simp only [List.foldl_cons]
    apply ih
    exact oneHighFamilyCollectAtomVal_old_mem R atom hmem

theorem oneHighFamilyCollectAtomsVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom) {acc : OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat} (hmem : entry ∈ acc.1.ids) :
    entry ∈ (oneHighFamilyCollectAtomsVal R atoms acc).2.1.ids := by
  exact oneHighFamilyCollectAtomsFoldVal_old_mem R atoms hmem

theorem oneHighFamilyListForall₂_append
    {A B : Type*} {r : A → B → Prop}
    {as as' : List A} {bs bs' : List B}
    (h₁ : List.Forall₂ r as bs) (h₂ : List.Forall₂ r as' bs') :
    List.Forall₂ r (as ++ as') (bs ++ bs') := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact .cons hr ih

theorem oneHighFamilyCollectedAtomsMatch_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atoms : List OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (hm : OneHighFamilyCollectedAtomsMatch atoms input)
    (hs : OneHighFamilySemanticSound R input.2) :
    OneHighFamilyInputAccumSound R input := by
  have aux : ∀ {as : List OneHighFamilyAtom} {ids : List Nat},
      List.Forall₂ (fun atom id => (atom, id) ∈ input.2.1.ids) as ids →
      ∀ id ∈ ids, ∃ atom, (atom, id) ∈ input.2.1.ids := by
    intro as ids h
    induction h with
    | nil => simp
    | cons hr _ ih =>
        intro id hid
        simp only [List.mem_cons] at hid
        rcases hid with rfl | hid
        · exact ⟨_, hr⟩
        · exact ih id hid
  have hidMem := aux hm.aligned
  refine ⟨hs, ?_, ?_⟩
  · intro lit hlit
    have hlit' : lit ∈ input.1.toList := by simpa using hlit
    rw [hm.vars_eq] at hlit'
    rcases List.mem_map.mp hlit' with ⟨id, hid, rfl⟩
    rcases hidMem id hid with ⟨atom, hatom⟩
    have hpos := (hs.ids.id_bounds _ hatom).1
    simpa using (Nat.ne_of_gt hpos)
  · intro lit hlit
    have hlit' : lit ∈ input.1.toList := by simpa using hlit
    rw [hm.vars_eq] at hlit'
    rcases List.mem_map.mp hlit' with ⟨id, hid, rfl⟩
    rcases hidMem id hid with ⟨atom, hatom⟩
    simpa using (hs.ids.id_bounds _ hatom).2

noncomputable def oneHighFamilyV2CombinedF2Match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a x : Nat) (acc : OneHighFamilyValState) :
    let saverInput := (oneHighFamilyV2SaverVertices a x).foldl
      (fun input w => oneHighFamilyV2SaverStepVal R x w input) (#[], acc)
    let commonInput := oneHighFamilyCollectAtomsVal R
      (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
    OneHighFamilyCollectedAtomsMatch
      (oneHighFamilyV2PairedCommonAtoms x ++ oneHighFamilyV2SaverAtoms a x)
      (commonInput.1 ++ saverInput.1, commonInput.2) := by
  dsimp only
  let saverInput := (oneHighFamilyV2SaverVertices a x).foldl
    (fun input w => oneHighFamilyV2SaverStepVal R x w input) (#[], acc)
  let commonInput := oneHighFamilyCollectAtomsVal R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  have hs := oneHighFamilyCollectSaversVal_match R x
    (oneHighFamilyV2SaverVertices a x) acc
  have hc := oneHighFamilyCollectAtomsVal_match R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  refine ⟨hc.ids ++ hs.ids, ?_, ?_⟩
  · simp only [Array.toList_append, List.map_append]
    rw [hc.vars_eq, hs.vars_eq]
  · apply oneHighFamilyListForall₂_append hc.aligned
    apply hs.aligned.imp
    intro atom id hid
    exact oneHighFamilyCollectAtomsVal_old_mem R
      (oneHighFamilyV2PairedCommonAtoms x) hid

structure OneHighFamilyV2F2Ledger
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (a : Nat) : Prop where
  count_eq : ∀ x, x < 40 →
    (((oneHighFamilyV2PairedCommonAtoms x ++
      oneHighFamilyV2SaverAtoms a x).map
        (oneHighFamilyAtomValue R)).count true) =
      oneHighFamilyFarDegreeBound a x

noncomputable def oneHighFamilyV2F2VertexStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a x : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let saverInput := (oneHighFamilyV2SaverVertices a x).foldl
    (fun input w => oneHighFamilyV2SaverStepVal R x w input) (#[], acc)
  let commonInput := oneHighFamilyCollectAtomsVal R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  let input := (commonInput.1 ++ saverInput.1, commonInput.2)
  oneHighFamilyEqualsBlockVal input.1
    (oneHighFamilyInputAccumRow input)
    (oneHighFamilyFarDegreeBound a x) input.2

theorem oneHighFamilyV2F2VertexStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a x : Nat) (hx : x < 40) (ledger : OneHighFamilyV2F2Ledger R a)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F2VertexStepVal R a x acc) := by
  let saverInput := (oneHighFamilyV2SaverVertices a x).foldl
    (fun input w => oneHighFamilyV2SaverStepVal R x w input) (#[], acc)
  let commonInput := oneHighFamilyCollectAtomsVal R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  let input : Array Int × OneHighFamilyValState :=
    (commonInput.1 ++ saverInput.1, commonInput.2)
  have hws : ∀ w ∈ oneHighFamilyV2SaverVertices a x, w < 40 := by
    intro w hw
    simp only [oneHighFamilyV2SaverVertices, List.mem_filter,
      List.mem_range] at hw
    exact hw.1
  have hb : (x / 5 ^^^ 1) < 8 := by
    let b : Fin 8 := ⟨x / 5, by omega⟩
    have hm := (oneHighStandardMate b).isLt
    rw [oneHighStandardMate_val_eq_xor] at hm
    simpa [b] using hm
  have hsSaver : OneHighFamilySemanticSound R saverInput.2 := by
    exact oneHighFamilyV2CollectSaversVal_semanticSound R hx hws hb hacc
  have hsCommon : OneHighFamilySemanticSound R commonInput.2 := by
    exact (oneHighFamilyCollectAtomsVal_sound R
      (oneHighFamilyV2PairedCommonAtoms x)
      (oneHighFamilyInputAccumSound_empty R hsSaver)).semantic
  have hm : OneHighFamilyCollectedAtomsMatch
      (oneHighFamilyV2PairedCommonAtoms x ++ oneHighFamilyV2SaverAtoms a x)
      input := oneHighFamilyV2CombinedF2Match R a x acc
  have hsInput : OneHighFamilyInputAccumSound R input :=
    oneHighFamilyCollectedAtomsMatch_sound R hm hsCommon
  unfold oneHighFamilyV2F2VertexStepVal
  change OneHighFamilySemanticSound R
    (oneHighFamilyEqualsBlockVal input.1
      (oneHighFamilyInputAccumRow input)
      (oneHighFamilyFarDegreeBound a x) input.2)
  apply oneHighFamilyEqualsBlockVal_semanticSound R hsInput.semantic
  · exact oneHighFamilyInputAccum_reifies R hsInput
  · calc
      seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
          (List.ofFn (oneHighFamilyInputAccumRow input)).count true :=
        seqPrefixTrue_oneHighFamilyLiteralRow_eq_countP input.2.2 input.1
      _ = (((oneHighFamilyV2PairedCommonAtoms x ++
          oneHighFamilyV2SaverAtoms a x).map
            (oneHighFamilyAtomValue R)).count true) := by
        rw [oneHighFamilyCollectedAtoms_values R hm hsInput.semantic]
      _ = oneHighFamilyFarDegreeBound a x := ledger.count_eq x hx

theorem oneHighFamilyV2F2VertexStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a x : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyV2F2VertexStepVal R a x acc).1 =
      oneHighFamilyV2F2VertexStep a x acc.1 := by
  let saverInput := (oneHighFamilyV2SaverVertices a x).foldl
    (fun input w => oneHighFamilyV2SaverStepVal R x w input) (#[], acc)
  let rawSaver := (oneHighFamilyV2SaverVertices a x).foldl
    (fun input w => oneHighFamilyV2SaverStep x w input) (#[], acc.1)
  have hs := oneHighFamilyV2CollectSaversVal_projection R x
    (oneHighFamilyV2SaverVertices a x) (#[], acc)
  change saverInput.1 = rawSaver.1 ∧ saverInput.2.1 = rawSaver.2 at hs
  let commonInput := oneHighFamilyCollectAtomsVal R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  let rawCommon := (oneHighFamilyBlockVertices (x / 5 ^^^ 1)).foldl
    (fun input z => oneHighFamilyV2CollectPairedCommonStep x z input)
    (#[], rawSaver.2)
  have hc₀ := oneHighFamilyCollectAtomsVal_projection R
    (oneHighFamilyV2PairedCommonAtoms x) saverInput.2
  let genericStep :=
    fun (input : Array Int × OneHighFamilyGenState) z =>
      let (vars, inputSt) := input
      let (c, st) := oneHighFamilyAtomId
        (.common (min x z) (max x z)) inputSt
      (vars.push (c : Int), st)
  have hstep :
      genericStep =
      (fun input z => oneHighFamilyV2CollectPairedCommonStep x z input) := by
    funext input z
    rfl
  have hc : commonInput.1 = rawCommon.1 ∧
      commonInput.2.1 = rawCommon.2 := by
    rw [show saverInput.2.1 = rawSaver.2 from hs.2] at hc₀
    let atomStep :=
      fun (input : Array Int × OneHighFamilyGenState)
          (atom : OneHighFamilyAtom) =>
        let (vars, inputSt) := input
        let (id, st) := oneHighFamilyAtomId atom inputSt
        (vars.push (id : Int), st)
    change commonInput.1 =
          ((oneHighFamilyV2PairedCommonAtoms x).foldl atomStep
            (#[], rawSaver.2)).1 ∧
        commonInput.2.1 =
          ((oneHighFamilyV2PairedCommonAtoms x).foldl atomStep
            (#[], rawSaver.2)).2 at hc₀
    have hfold :
        (oneHighFamilyV2PairedCommonAtoms x).foldl atomStep
            (#[], rawSaver.2) =
          (oneHighFamilyBlockVertices (x / 5 ^^^ 1)).foldl
            genericStep (#[], rawSaver.2) := by
      rw [oneHighFamilyV2PairedCommonAtoms, List.foldl_map]
    rw [hfold, hstep] at hc₀
    exact hc₀
  unfold oneHighFamilyV2F2VertexStepVal oneHighFamilyV2F2VertexStep
  rw [oneHighFamilyEqualsBlockVal_state]
  change oneHighFamilyEqualsBlock
      (commonInput.1 ++ saverInput.1)
      (oneHighFamilyFarDegreeBound a x) commonInput.2.1 = _
  rw [hc.1, hc.2, hs.1]

noncomputable def oneHighFamilyV2F2ClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40)
    (oneHighFamilyV2F2VertexStepVal R a)
    (oneHighFamilyV2PairedCommonClausesVal R a val)

theorem oneHighFamilyV2F2ClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (f₁ : OneHighFamilyV2F1Ledger a R)
    (f₂ : OneHighFamilyV2F2Ledger R a)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F2ClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2PairedCommonClausesVal_semanticSound
      R a hc f₁ val)
  intro x hx acc hacc
  exact oneHighFamilyV2F2VertexStepVal_semanticSound R a x
    (List.mem_range.mp hx) f₂ hacc

theorem oneHighFamilyV2F2ClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2F2ClausesVal R a val).1 =
      oneHighFamilyV2F2Clauses a (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2F2ClausesVal oneHighFamilyV2F2Clauses
  calc
    _ = oneHighFamilyRunList (List.range 40)
        (oneHighFamilyV2F2VertexStep a)
        (oneHighFamilyV2PairedCommonClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun x acc => oneHighFamilyV2F2VertexStepVal_state R a x acc)
    _ = _ := by rw [oneHighFamilyV2PairedCommonClausesVal_state]

def oneHighFamilyV2F3aAtoms (pair : Nat) : List OneHighFamilyAtom :=
  (oneHighFamilyBlockVertices (2 * pair)).flatMap fun x =>
    (oneHighFamilyBlockVertices (2 * pair + 1)).map fun z =>
      .common (min x z) (max x z)

structure OneHighFamilyV2F3aLedger
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (a : Nat) : Prop where
  count_eq : ∀ pair, pair < 4 →
    ((oneHighFamilyV2F3aAtoms pair).map
        (oneHighFamilyAtomValue R)).count true =
      30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
        2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1)

theorem oneHighFamilyFoldl_flatMap
    {A B C : Type*} (xs : List A) (f : A → List B)
    (step : C → B → C) (init : C) :
    (xs.flatMap f).foldl step init =
      xs.foldl (fun acc x => (f x).foldl step acc) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih _

noncomputable def oneHighFamilyV2CollectPairedCommonStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (input : Array Int × OneHighFamilyValState) :=
  oneHighFamilyCollectAtomVal R
    (.common (min x z) (max x z)) input

theorem oneHighFamilyV2CollectPairedCommonStepVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyV2CollectPairedCommonStepVal R x z input
    let raw := oneHighFamilyV2CollectPairedCommonStep x z
      (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  exact oneHighFamilyCollectAtomVal_projection R
    (.common (min x z) (max x z)) input

theorem oneHighFamilyV2CollectPairedCommonInnerVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Nat) (zs : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := zs.foldl (fun input z =>
      oneHighFamilyV2CollectPairedCommonStepVal R x z input) input
    let raw := zs.foldl (fun input z =>
      oneHighFamilyV2CollectPairedCommonStep x z input)
      (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction zs generalizing input with
  | nil => simp
  | cons z zs ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyV2CollectPairedCommonStepVal_projection
        R x z input
      have hi := ih (oneHighFamilyV2CollectPairedCommonStepVal R x z input)
      rcases hp with ⟨hvars, hstate⟩
      simpa [hvars, hstate] using hi

noncomputable def oneHighFamilyV2F3aCollectVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (acc : OneHighFamilyValState) :=
  (oneHighFamilyBlockVertices (2 * pair)).foldl (fun input x =>
    (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun input z => oneHighFamilyV2CollectPairedCommonStepVal R x z input)
      input) (#[], acc)

theorem oneHighFamilyV2CollectPairedCommonOuterVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (xs zs : List Nat) (input : Array Int × OneHighFamilyValState) :
    let out := xs.foldl (fun input x => zs.foldl
      (fun input z => oneHighFamilyV2CollectPairedCommonStepVal R x z input)
      input) input
    let raw := xs.foldl (fun input x => zs.foldl
      (fun input z => oneHighFamilyV2CollectPairedCommonStep x z input)
      input) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction xs generalizing input with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyV2CollectPairedCommonInnerVal_projection R x
        zs input
      have hi := ih (zs.foldl (fun input z =>
        oneHighFamilyV2CollectPairedCommonStepVal R x z input) input)
      rcases hp with ⟨hvars, hstate⟩
      simpa [hvars, hstate] using hi

theorem oneHighFamilyV2F3aCollectVal_eq_collectAtomsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (acc : OneHighFamilyValState) :
    oneHighFamilyV2F3aCollectVal R pair acc =
      oneHighFamilyCollectAtomsVal R (oneHighFamilyV2F3aAtoms pair) acc := by
  unfold oneHighFamilyV2F3aCollectVal oneHighFamilyCollectAtomsVal
    oneHighFamilyV2F3aAtoms
  rw [oneHighFamilyFoldl_flatMap]
  simp only [List.foldl_map,
    oneHighFamilyV2CollectPairedCommonStepVal]

theorem oneHighFamilyV2F3aCollectVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (acc : OneHighFamilyValState) :
    let out := oneHighFamilyV2F3aCollectVal R pair acc
    let raw := oneHighFamilyV2F3aCollect pair acc.1
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  unfold oneHighFamilyV2F3aCollectVal oneHighFamilyV2F3aCollect
  exact oneHighFamilyV2CollectPairedCommonOuterVal_projection R
    (oneHighFamilyBlockVertices (2 * pair))
    (oneHighFamilyBlockVertices (2 * pair + 1)) (#[], acc)

noncomputable def oneHighFamilyV2F3aFinishVal
    (a pair : Nat) (input : Array Int × OneHighFamilyValState) :
    OneHighFamilyValState :=
  let bound := 30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
      2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1)
  oneHighFamilyEqualsBlockVal input.1
    (oneHighFamilyInputAccumRow input) bound input.2

noncomputable def oneHighFamilyV2F3aBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a pair : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyV2F3aFinishVal a pair
    (oneHighFamilyV2F3aCollectVal R pair acc)

theorem oneHighFamilyV2F3aFinishVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a pair : Nat) {input : Array Int × OneHighFamilyValState}
    (hsInput : OneHighFamilyInputAccumSound R input)
    (hcount : seqPrefixTrue (oneHighFamilyInputAccumRow input)
      input.1.size =
        30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
          2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F3aFinishVal a pair input) := by
  unfold oneHighFamilyV2F3aFinishVal
  apply oneHighFamilyEqualsBlockVal_semanticSound R hsInput.semantic
  · exact oneHighFamilyInputAccum_reifies R hsInput
  · exact hcount

theorem oneHighFamilyV2F3aFinishVal_state
    (a pair : Nat) (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyV2F3aFinishVal a pair input).1 =
      oneHighFamilyV2F3aFinish a pair (input.1, input.2.1) := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyV2F3aFinishVal, oneHighFamilyV2F3aFinish]
  exact oneHighFamilyEqualsBlockVal_state vars _ _ st val

theorem oneHighFamilyV2F3aBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (ledger : OneHighFamilyV2F3aLedger R a)
    {pair : Nat} (hpair : pair < 4) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F3aBlockStepVal R a pair acc) := by
  let input := oneHighFamilyV2F3aCollectVal R pair acc
  have heq := oneHighFamilyV2F3aCollectVal_eq_collectAtomsVal R pair acc
  have hsGeneric := oneHighFamilyCollectAtomsVal_sound R
    (oneHighFamilyV2F3aAtoms pair)
    (oneHighFamilyInputAccumSound_empty R hacc)
  have hsInput : OneHighFamilyInputAccumSound R input := by
    change OneHighFamilyInputAccumSound R
      (oneHighFamilyV2F3aCollectVal R pair acc)
    rw [heq]
    exact hsGeneric
  apply oneHighFamilyV2F3aFinishVal_semanticSound R a pair hsInput
  calc
    seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
        (List.ofFn (oneHighFamilyInputAccumRow input)).count true :=
      seqPrefixTrue_oneHighFamilyLiteralRow_eq_countP input.2.2 input.1
    _ = ((oneHighFamilyV2F3aAtoms pair).map
        (oneHighFamilyAtomValue R)).count true := by
      rw [show input = oneHighFamilyCollectAtomsVal R
        (oneHighFamilyV2F3aAtoms pair) acc from heq]
      rw [oneHighFamilyCollectedAtoms_values R
        (oneHighFamilyCollectAtomsVal_match R
          (oneHighFamilyV2F3aAtoms pair) acc) hsGeneric.semantic]
    _ = _ := ledger.count_eq pair hpair

theorem oneHighFamilyV2F3aBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a pair : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyV2F3aBlockStepVal R a pair acc).1 =
      oneHighFamilyV2F3aBlockStep a pair acc.1 := by
  generalize hv : oneHighFamilyV2F3aCollectVal R pair acc = input
  rcases input with ⟨vars, valAcc⟩
  generalize hg : oneHighFamilyV2F3aCollect pair acc.1 = raw
  rcases raw with ⟨rawVars, rawSt⟩
  have hp := oneHighFamilyV2F3aCollectVal_projection R pair acc
  rw [hv, hg] at hp
  rcases hp with ⟨rfl, rfl⟩
  rw [show oneHighFamilyV2F3aBlockStepVal R a pair acc =
    oneHighFamilyV2F3aFinishVal a pair (vars, valAcc) by
      simp only [oneHighFamilyV2F3aBlockStepVal, hv]]
  rw [oneHighFamilyV2F3aFinishVal_state]
  simp only [oneHighFamilyV2F3aBlockStep, hg]

noncomputable def oneHighFamilyV2F3aClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 4)
    (oneHighFamilyV2F3aBlockStepVal R a)
    (oneHighFamilyV2F2ClausesVal R a val)

theorem oneHighFamilyV2F3aClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (f₁ : OneHighFamilyV2F1Ledger a R)
    (f₂ : OneHighFamilyV2F2Ledger R a)
    (f₃a : OneHighFamilyV2F3aLedger R a)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F3aClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2F2ClausesVal_semanticSound R a hc f₁ f₂ val)
  intro pair hpair acc hacc
  exact oneHighFamilyV2F3aBlockStepVal_semanticSound a R f₃a
    (List.mem_range.mp hpair) hacc

theorem oneHighFamilyV2F3aClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2F3aClausesVal R a val).1 =
      oneHighFamilyV2F3aClauses a (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyV2F3aClausesVal oneHighFamilyV2F3aClauses
  calc
    _ = oneHighFamilyRunList (List.range 4)
        (oneHighFamilyV2F3aBlockStep a)
        (oneHighFamilyV2F2ClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyV2F3aBlockStepVal_state R a pair acc)
    _ = _ := by rw [oneHighFamilyV2F2ClausesVal_state]

noncomputable def oneHighFamilyV2AppendEdgeVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  oneHighFamilyCollectAtomVal R (.edge (min i j) (max i j)) input

theorem oneHighFamilyV2AppendEdgeVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyV2AppendEdgeVal R i j input
    let raw := oneHighFamilyV2AppendEdge i j (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  exact oneHighFamilyCollectAtomVal_projection R
    (.edge (min i j) (max i j)) input

noncomputable def oneHighFamilyV2MaybeAppendEdgeVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (enabled : Bool) (i j : Nat)
    (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  if enabled then oneHighFamilyV2AppendEdgeVal R i j input else input

theorem oneHighFamilyV2MaybeAppendEdgeVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (enabled : Bool) (i j : Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyV2MaybeAppendEdgeVal R enabled i j input
    let raw := oneHighFamilyV2MaybeAppendEdge enabled i j
      (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  simp only [oneHighFamilyV2MaybeAppendEdgeVal,
    oneHighFamilyV2MaybeAppendEdge]
  split
  · exact oneHighFamilyV2AppendEdgeVal_projection R i j input
  · exact ⟨rfl, rfl⟩

theorem oneHighFamilyV2AppendEdgeVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) {input : Array Int × OneHighFamilyValState}
    (hinput : OneHighFamilyInputAccumSound R input) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyV2AppendEdgeVal R i j input) := by
  exact oneHighFamilyCollectAtomVal_sound R hinput
    (.edge (min i j) (max i j))

theorem oneHighFamilyV2MaybeAppendEdgeVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (enabled : Bool) (i j : Nat)
    {input : Array Int × OneHighFamilyValState}
    (hinput : OneHighFamilyInputAccumSound R input) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyV2MaybeAppendEdgeVal R enabled i j input) := by
  simp only [oneHighFamilyV2MaybeAppendEdgeVal]
  split
  · exact oneHighFamilyV2AppendEdgeVal_semanticSound R i j hinput
  · exact hinput

noncomputable def oneHighFamilyV2CollectedMidpointsAtomsMatch
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (ws : List Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedAtomsMatch
      (ws.map (fun w => .midpoint (min x z) w (max x z)))
      (oneHighFamilyCollectMidpointsVal R x z ws acc) := by
  let hm := oneHighFamilyCollectMidpointsVal_match R x z ws acc
  exact {
    ids := hm.ids
    vars_eq := hm.vars_eq
    aligned := by
      simpa only [List.forall₂_map_left_iff] using hm.aligned }

noncomputable def oneHighFamilyV2MaybeAppendEdgeVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (enabled : Bool) (i j : Nat)
    {atoms : List OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedAtomsMatch atoms input) :
    OneHighFamilyCollectedAtomsMatch
      (atoms ++ if enabled then [(.edge (min i j) (max i j))] else [])
      (oneHighFamilyV2MaybeAppendEdgeVal R enabled i j input) := by
  simp only [oneHighFamilyV2MaybeAppendEdgeVal]
  split
  · simpa [oneHighFamilyV2AppendEdgeVal] using
      oneHighFamilyCollectedAtomsMatch_push R h
  · simpa using h

noncomputable def oneHighFamilyV2FinishCommonVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (cs ors : Array Int) (x z : Nat) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (c, acc) := oneHighFamilyAtomIdVal R
    (.common (min x z) (max x z)) acc
  let acc := (oneHighFamilyEmitVal (-(c : Int) :: ors.toList) acc).2
  let acc := ors.foldl
    (fun acc lit => (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) acc
  (cs.push (c : Int), acc)

theorem oneHighFamilyV2FinishCommonVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (cs ors : Array Int) (x z : Nat)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc)
    (hpos : ∀ lit ∈ ors, 0 < lit)
    (hbound : ∀ lit ∈ ors, lit.natAbs ≤ acc.1.top)
    (hiff : ∀ c accC,
      oneHighFamilyAtomIdVal R
        (.common (min x z) (max x z)) acc = (c, accC) →
      (accC.2 c = true ↔ ∃ lit ∈ ors, accC.2 lit.natAbs = true)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2FinishCommonVal R cs ors x z acc).2 := by
  let atom := OneHighFamilyAtom.common (min x z) (max x z)
  generalize hout : oneHighFamilyAtomIdVal R atom acc = out
  rcases out with ⟨c, accC⟩
  have hsC := oneHighFamilyAtomIdVal_semanticSound R hacc atom
  rw [hout] at hsC
  have hrC := oneHighFamilyAtomIdVal_result R atom acc.1 acc.2
  rw [hout] at hrC
  have hstateEq : accC.1 = (oneHighFamilyAtomId atom acc.1).2 := by
    have h := oneHighFamilyAtomIdVal_state R atom acc.1 acc.2
    rw [hout] at h
    exact h
  have hcPos := (hsC.ids.id_bounds _ hrC.1).1
  have hcBound := (hsC.ids.id_bounds _ hrC.1).2
  let accOr := (oneHighFamilyEmitVal (-(c : Int) :: ors.toList) accC).2
  have hsOr : OneHighFamilySemanticSound R accOr := by
    apply oneHighFamilyEmitVal_semanticSound R hsC
    · cases hcval : accC.2 c
      · refine ⟨-(c : Int), by simp, ?_⟩
        simp [dimacsLitValue, hcval]
      · rcases (hiff c accC hout).mp hcval with ⟨lit, hlit, htrue⟩
        refine ⟨lit, by simp [hlit], ?_⟩
        have hlitPos := hpos lit hlit
        simp [dimacsLitValue, hlitPos, htrue]
    · intro lit hlit
      simp only [List.mem_cons] at hlit
      rcases hlit with rfl | hlit
      · simpa using hcBound
      · have hm : lit ∈ ors := by simpa using hlit
        exact le_trans (hbound lit hm)
          (by rw [hstateEq]; exact oneHighFamilyAtomId_top_le atom acc.1)
  have hfold : OneHighFamilySemanticSound R
      (ors.foldl (fun acc lit =>
        (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) accOr) := by
    have aux : ∀ (l : List Int), (∀ lit ∈ l, lit ∈ ors) →
        ∀ start : OneHighFamilyValState,
        start.2 = accC.2 → start.1.top = accC.1.top →
        OneHighFamilySemanticSound R start →
        OneHighFamilySemanticSound R
          (l.foldl (fun acc lit =>
            (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) start) := by
      intro l hl
      induction l with
      | nil => intro start _ _ hs; exact hs
      | cons lit lits ih =>
        intro start hval htop hs
        simp only [List.foldl_cons]
        have hnext := oneHighFamilyEmitVal_semanticSound R hs
          [-lit, (c : Int)]
        have hsNext : OneHighFamilySemanticSound R
            (oneHighFamilyEmitVal [-lit, (c : Int)] start).2 := by
          apply hnext
          · by_cases ht : start.2 lit.natAbs = true
            · have hm : lit ∈ ors := hl lit (by simp)
              have hcTrueC : accC.2 c = true := by
                apply (hiff c accC hout).mpr
                refine ⟨lit, hm, ?_⟩
                rw [← hval]
                exact ht
              have hcTrue : start.2 c = true := by
                rw [hval]
                exact hcTrueC
              refine ⟨(c : Int), by simp, ?_⟩
              simp [dimacsLitValue, hcTrue, hcPos]
            · refine ⟨-lit, by simp, ?_⟩
              have hm : lit ∈ ors := hl lit (by simp)
              have hge : 0 ≤ lit := le_of_lt (hpos lit hm)
              simp [dimacsLitValue, hge, ht]
          · intro q hq
            simp at hq
            rcases hq with rfl | rfl
            · have hm : lit ∈ ors := hl lit (by simp)
              have hb : (-lit).natAbs ≤ accC.1.top := by
                rw [Int.natAbs_neg]
                exact le_trans (hbound lit hm) (by
                  rw [hstateEq]
                  exact oneHighFamilyAtomId_top_le atom acc.1)
              rw [htop]
              simpa using hb
            · rw [htop]
              exact hcBound
        apply ih (by
          intro q hq
          exact hl q (by simp [hq]))
        · exact hval
        · exact htop
        exact hsNext
    rw [← Array.foldl_toList]
    exact aux ors.toList (by intro lit hlit; simpa using hlit) accOr
      rfl rfl hsOr
  simpa [oneHighFamilyV2FinishCommonVal, atom, hout, accOr] using hfold

theorem oneHighFamilyV2FinishCommonFoldVal_state
    (ors : Array Int) (c : Nat) (acc : OneHighFamilyValState)
    (st : OneHighFamilyGenState) (hstate : acc.1 = st) :
    (ors.foldl (fun acc lit =>
      (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) acc).1 =
    ors.foldl (fun st lit =>
      (oneHighFamilyEmit [-lit, (c : Int)] st).2) st := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction ors.toList generalizing acc st with
  | nil => exact hstate
  | cons lit lits ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [oneHighFamilyEmitVal_state]
      exact congrArg
        (fun s => (oneHighFamilyEmit [-lit, (c : Int)] s).2) hstate

theorem oneHighFamilyV2FinishCommonVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (cs ors : Array Int) (x z : Nat) (acc : OneHighFamilyValState) :
    let out := oneHighFamilyV2FinishCommonVal R cs ors x z acc
    let raw := oneHighFamilyV2FinishCommon cs ors x z acc.1
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  generalize hv : oneHighFamilyAtomIdVal R
    (.common (min x z) (max x z)) acc = outV
  rcases outV with ⟨c, accC⟩
  generalize hg : oneHighFamilyCommonAtomId x z acc.1 = outG
  rcases outG with ⟨cg, stC⟩
  have hid := oneHighFamilyAtomIdVal_id R
    (.common (min x z) (max x z)) acc.1 acc.2
  have hstate := oneHighFamilyAtomIdVal_state R
    (.common (min x z) (max x z)) acc.1 acc.2
  rw [hv] at hid hstate
  have hg' : oneHighFamilyAtomId
      (.common (min x z) (max x z)) acc.1 = (cg, stC) := by
    simpa [oneHighFamilyCommonAtomId] using hg
  rw [hg'] at hid hstate
  dsimp at hid hstate
  subst cg
  simp only [oneHighFamilyV2FinishCommonVal,
    oneHighFamilyV2FinishCommon, hv, hg]
  constructor
  · trivial
  · apply oneHighFamilyV2FinishCommonFoldVal_state
    rw [oneHighFamilyEmitVal_state]
    exact congrArg
      (fun s => (oneHighFamilyEmit (-((c : Nat) : Int) :: ors.toList) s).2)
      hstate

def oneHighFamilyV2UnpairedCandidateAtoms
    (profile a b x z : Nat) : List OneHighFamilyAtom :=
  (oneHighFamilyV2UnpairedMidpoints a b).map
      (fun w => .midpoint (min x z) w (max x z)) ++
    (if oneHighFamilyVertexMatched profile x then
      [(.edge (min (oneHighFamilyV2PartnerVertex x) z)
        (max (oneHighFamilyV2PartnerVertex x) z))] else []) ++
    (if oneHighFamilyVertexMatched profile z then
      [(.edge (min x (oneHighFamilyV2PartnerVertex z))
        (max x (oneHighFamilyV2PartnerVertex z)))] else [])

noncomputable def oneHighFamilyV2UnpairedCandidateInputVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x z : Nat) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let midInput := (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun input w => oneHighFamilyMidpointTseitinStepVal R x z w input)
    (#[], acc)
  let xInput := oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z midInput
  oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) xInput

noncomputable def oneHighFamilyV2UnpairedCandidateInputVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x z : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedAtomsMatch
      (oneHighFamilyV2UnpairedCandidateAtoms profile a b x z)
      (oneHighFamilyV2UnpairedCandidateInputVal R profile a b x z acc) := by
  let mids := oneHighFamilyV2UnpairedMidpoints a b
  let midInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  let hm := oneHighFamilyV2CollectedMidpointsAtomsMatch R x z mids acc
  let xInput := oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z midInput
  let hx := oneHighFamilyV2MaybeAppendEdgeVal_match R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z hm
  let hz := oneHighFamilyV2MaybeAppendEdgeVal_match R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) hx
  simpa [oneHighFamilyV2UnpairedCandidateAtoms,
    oneHighFamilyV2UnpairedCandidateInputVal, mids, midInput, xInput,
    oneHighFamilyCollectMidpointsVal, List.append_assoc] using hz

theorem oneHighFamilyV2UnpairedCandidateInputVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b : Nat) {x z : Nat}
    (hx : x < 40) (hz : z < 40) (hxz : x < z)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyV2UnpairedCandidateInputVal R profile a b x z acc) := by
  let mids := oneHighFamilyV2UnpairedMidpoints a b
  let midInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  have hsMid : OneHighFamilySemanticSound R midInput.2 := by
    apply oneHighFamilyCollectMidpointsVal_semanticSound R hx hz hxz mids
    · intro w hw
      exact List.mem_range.mp (List.mem_filter.mp hw).1
    · exact hacc
  have hm := oneHighFamilyV2CollectedMidpointsAtomsMatch R x z mids acc
  have hiMid := oneHighFamilyCollectedAtomsMatch_sound R hm hsMid
  have hiX := oneHighFamilyV2MaybeAppendEdgeVal_semanticSound R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z hiMid
  have hiZ := oneHighFamilyV2MaybeAppendEdgeVal_semanticSound R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) hiX
  simpa [oneHighFamilyV2UnpairedCandidateInputVal, mids, midInput,
    oneHighFamilyCollectMidpointsVal] using hiZ

noncomputable def oneHighFamilyV2UnpairedCommonStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x z : Nat)
    (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (cs, acc) := input
  let midInput := (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun input w => oneHighFamilyMidpointTseitinStepVal R x z w input)
    (#[], acc)
  let xInput := oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z midInput
  let zInput := oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) xInput
  oneHighFamilyV2FinishCommonVal R cs zInput.1 x z zInput.2

theorem oneHighFamilyV2UnpairedCommonStepVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x z : Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyV2UnpairedCommonStepVal R
      profile a b x z input
    let raw := oneHighFamilyV2UnpairedCommonStep
      profile a b x z (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  rcases input with ⟨cs, acc⟩
  let mids := oneHighFamilyV2UnpairedMidpoints a b
  generalize hmV : mids.foldl (fun input w =>
    oneHighFamilyMidpointTseitinStepVal R x z w input) (#[], acc) = midV
  rcases midV with ⟨orsV, accM⟩
  generalize hmG : mids.foldl (fun input w =>
    oneHighFamilyMidpointTseitinStep x z w input) (#[], acc.1) = midG
  rcases midG with ⟨orsG, stM⟩
  have hm := oneHighFamilyCollectMidpointsVal_projection R x z mids (#[], acc)
  rw [hmV, hmG] at hm
  rcases hm with ⟨rfl, rfl⟩
  generalize hxV : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (orsV, accM) = xV
  rcases xV with ⟨orsXV, accX⟩
  generalize hxG : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (orsV, accM.1) = xG
  rcases xG with ⟨orsXG, stX⟩
  have hx := oneHighFamilyV2MaybeAppendEdgeVal_projection R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (orsV, accM)
  rw [hxV, hxG] at hx
  rcases hx with ⟨rfl, rfl⟩
  generalize hzV : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (orsXV, accX) = zV
  rcases zV with ⟨orsZV, accZ⟩
  generalize hzG : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (orsXV, accX.1) = zG
  rcases zG with ⟨orsZG, stZ⟩
  have hz := oneHighFamilyV2MaybeAppendEdgeVal_projection R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (orsXV, accX)
  rw [hzV, hzG] at hz
  rcases hz with ⟨rfl, rfl⟩
  have hf := oneHighFamilyV2FinishCommonVal_projection R
    cs orsZV x z accZ
  simp only [oneHighFamilyV2UnpairedCommonStepVal,
    oneHighFamilyV2UnpairedCommonStep, mids, hmV, hmG, hxV, hxG,
    hzV, hzG]
  exact hf

theorem oneHighFamilyV2UnpairedCommonInnerVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x : Nat) (zs : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := zs.foldl (fun input z =>
      oneHighFamilyV2UnpairedCommonStepVal R
        profile a b x z input) input
    let raw := zs.foldl (fun input z =>
      oneHighFamilyV2UnpairedCommonStep profile a b x z input)
      (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction zs generalizing input with
  | nil => simp
  | cons z zs ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyV2UnpairedCommonStepVal_projection R
        profile a b x z input
      have hi := ih (oneHighFamilyV2UnpairedCommonStepVal R
        profile a b x z input)
      rcases hp with ⟨hvars, hstate⟩
      simpa [hvars, hstate] using hi

theorem oneHighFamilyV2UnpairedCommonOuterVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b : Nat) (xs zs : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := xs.foldl (fun input x => zs.foldl
      (fun input z => oneHighFamilyV2UnpairedCommonStepVal R
        profile a b x z input) input) input
    let raw := xs.foldl (fun input x => zs.foldl
      (fun input z => oneHighFamilyV2UnpairedCommonStep
        profile a b x z input) input) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction xs generalizing input with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyV2UnpairedCommonInnerVal_projection R
        profile a b x zs input
      have hi := ih (zs.foldl (fun input z =>
        oneHighFamilyV2UnpairedCommonStepVal R
          profile a b x z input) input)
      rcases hp with ⟨hvars, hstate⟩
      simpa [hvars, hstate] using hi

noncomputable def oneHighFamilyV2F3bCollectVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  (oneHighFamilyBlockVertices pair.1).foldl (fun input x =>
    (oneHighFamilyBlockVertices pair.2).foldl (fun input z =>
      oneHighFamilyV2UnpairedCommonStepVal R
        profile pair.1 pair.2 x z input) input) (#[], acc)

theorem oneHighFamilyV2F3bCollectVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) :
    let out := oneHighFamilyV2F3bCollectVal R profile pair acc
    let raw := oneHighFamilyV2F3bCollect profile pair acc.1
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  unfold oneHighFamilyV2F3bCollectVal oneHighFamilyV2F3bCollect
  exact oneHighFamilyV2UnpairedCommonOuterVal_projection R
    profile pair.1 pair.2
    (oneHighFamilyBlockVertices pair.1)
    (oneHighFamilyBlockVertices pair.2) (#[], acc)

noncomputable def oneHighFamilyV2F3bFinishVal
    (table : OneHighMissTable) (pair : Nat × Nat)
    (input : Array Int × OneHighFamilyValState) :
    OneHighFamilyValState :=
  let bound := 20 + oneHighFamilyTableGet table pair.1 (pair.2 ^^^ 1) +
    oneHighFamilyTableGet table pair.2 (pair.1 ^^^ 1)
  if bound ≤ input.1.size then
    oneHighFamilyEqualsBlockVal input.1
      (oneHighFamilyInputAccumRow input) bound input.2 else input.2

theorem oneHighFamilyV2F3bFinishVal_state
    (table : OneHighMissTable) (pair : Nat × Nat)
    (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyV2F3bFinishVal table pair input).1 =
      oneHighFamilyV2F3bFinish table pair (input.1, input.2.1) := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyV2F3bFinishVal, oneHighFamilyV2F3bFinish]
  split
  · exact oneHighFamilyEqualsBlockVal_state vars _ _ st val
  · rfl

theorem oneHighFamilyV2F3bFinishVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (table : OneHighMissTable) (pair : Nat × Nat)
    {input : Array Int × OneHighFamilyValState}
    (hsInput : OneHighFamilyInputAccumSound R input)
    (hcount : 20 + oneHighFamilyTableGet table pair.1 (pair.2 ^^^ 1) +
        oneHighFamilyTableGet table pair.2 (pair.1 ^^^ 1) ≤ input.1.size →
      seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
        20 + oneHighFamilyTableGet table pair.1 (pair.2 ^^^ 1) +
          oneHighFamilyTableGet table pair.2 (pair.1 ^^^ 1)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F3bFinishVal table pair input) := by
  unfold oneHighFamilyV2F3bFinishVal
  dsimp only
  split
  next hle =>
    apply oneHighFamilyEqualsBlockVal_semanticSound R hsInput.semantic
    · exact oneHighFamilyInputAccum_reifies R hsInput
    · exact hcount hle
  next => exact hsInput.semantic

structure OneHighFamilyV2F3bLedger
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) : Prop where
  collect_sound : ∀ pair, pair ∈ oneHighFamilyTablePairs → ∀ acc,
    OneHighFamilySemanticSound R acc →
    OneHighFamilyInputAccumSound R
      (oneHighFamilyV2F3bCollectVal R profile pair acc)
  count_eq : ∀ pair, pair ∈ oneHighFamilyTablePairs → ∀ acc,
    OneHighFamilySemanticSound R acc →
    let input := oneHighFamilyV2F3bCollectVal R profile pair acc
    20 + oneHighFamilyTableGet (oneHighFamilyGraphTable R profile)
          pair.1 (pair.2 ^^^ 1) +
        oneHighFamilyTableGet (oneHighFamilyGraphTable R profile)
          pair.2 (pair.1 ^^^ 1) ≤ input.1.size →
      seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
        20 + oneHighFamilyTableGet (oneHighFamilyGraphTable R profile)
          pair.1 (pair.2 ^^^ 1) +
        oneHighFamilyTableGet (oneHighFamilyGraphTable R profile)
          pair.2 (pair.1 ^^^ 1)

noncomputable def oneHighFamilyV2F3bBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyV2F3bFinishVal table pair
    (oneHighFamilyV2F3bCollectVal R profile pair acc)

theorem oneHighFamilyV2F3bBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyV2F3bBlockStepVal R profile table pair acc).1 =
      oneHighFamilyV2F3bBlockStep profile table pair acc.1 := by
  generalize hv : oneHighFamilyV2F3bCollectVal R profile pair acc = input
  rcases input with ⟨vars, valAcc⟩
  generalize hg : oneHighFamilyV2F3bCollect profile pair acc.1 = raw
  rcases raw with ⟨rawVars, rawSt⟩
  have hp := oneHighFamilyV2F3bCollectVal_projection R profile pair acc
  rw [hv, hg] at hp
  rcases hp with ⟨rfl, rfl⟩
  rw [show oneHighFamilyV2F3bBlockStepVal R profile table pair acc =
    oneHighFamilyV2F3bFinishVal table pair (vars, valAcc) by
      simp only [oneHighFamilyV2F3bBlockStepVal, hv]]
  rw [oneHighFamilyV2F3bFinishVal_state]
  simp only [oneHighFamilyV2F3bBlockStep, hg]

theorem oneHighFamilyV2F3bBlockStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (ledger : OneHighFamilyV2F3bLedger R profile)
    (pair : Nat × Nat) {acc : OneHighFamilyValState}
    (hpair : pair ∈ oneHighFamilyTablePairs)
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2F3bBlockStepVal R profile
        (oneHighFamilyGraphTable R profile) pair acc) := by
  let input := oneHighFamilyV2F3bCollectVal R profile pair acc
  apply oneHighFamilyV2F3bFinishVal_semanticSound R
    (oneHighFamilyGraphTable R profile) pair
    (ledger.collect_sound pair hpair acc hacc)
  exact ledger.count_eq pair hpair acc hacc

noncomputable def oneHighFamilyV2ClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal oneHighFamilyTablePairs
    (oneHighFamilyV2F3bBlockStepVal R profile (oneHighFamilyGraphTable R profile))
    (oneHighFamilyV2F3aClausesVal R profile val)

theorem oneHighFamilyV2ClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (val : DimacsValuation) :
    (oneHighFamilyV2ClausesVal R profile val).1 =
      oneHighFamilyV2Clauses profile
        (oneHighFamilyGraphTable R profile) := by
  unfold oneHighFamilyV2ClausesVal oneHighFamilyV2Clauses
  calc
    _ = oneHighFamilyRunList oneHighFamilyTablePairs
        (oneHighFamilyV2F3bBlockStep profile
          (oneHighFamilyGraphTable R profile))
        (oneHighFamilyV2F3aClausesVal R profile val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyV2F3bBlockStepVal_state R
          profile (oneHighFamilyGraphTable R profile) pair acc)
    _ = _ := by rw [oneHighFamilyV2F3aClausesVal_state]

theorem oneHighFamilyV2ClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (hc : OneHighPureFamilyCnfConstraints profile R)
    (f₁ : OneHighFamilyV2F1Ledger profile R)
    (f₂ : OneHighFamilyV2F2Ledger R profile)
    (f₃a : OneHighFamilyV2F3aLedger R profile)
    (f₃b : OneHighFamilyV2F3bLedger R profile)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyV2ClausesVal R profile val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyV2F3aClausesVal_semanticSound
      R profile hc f₁ f₂ f₃a val)
  intro pair hpair acc hacc
  exact oneHighFamilyV2F3bBlockStepVal_semanticSound
    R profile f₃b pair hpair hacc

theorem oneHighFamilyV2Clauses_dimacsSatisfiable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (hc : OneHighPureFamilyCnfConstraints profile R)
    (f₁ : OneHighFamilyV2F1Ledger profile R)
    (f₂ : OneHighFamilyV2F2Ledger R profile)
    (f₃a : OneHighFamilyV2F3aLedger R profile)
    (f₃b : OneHighFamilyV2F3bLedger R profile) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val
        (oneHighFamilyV2Clauses profile
          (oneHighFamilyGraphTable R profile)).clauses := by
  let initial : DimacsValuation := fun _ => false
  let out := oneHighFamilyV2ClausesVal R profile initial
  have hs := oneHighFamilyV2ClausesVal_semanticSound
    R profile hc f₁ f₂ f₃a f₃b initial
  have hstate := oneHighFamilyV2ClausesVal_state R profile initial
  refine ⟨out.2, ?_⟩
  rw [← hstate]
  exact hs.satisfied

def OneHighFamilyV2DimacsUnsat
    (profile : Nat) (table : OneHighMissTable) : Prop :=
  ∀ val : DimacsValuation,
    ¬dimacsFormulaSatisfied val
      (oneHighFamilyV2Clauses profile table).clauses

theorem oneHighFamilyV2_constraints_false_of_dimacsUnsat
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (table : OneHighMissTable)
    (hc : OneHighPureFamilyCnfConstraints profile R)
    (htable : oneHighFamilyGraphTable R profile = table)
    (f₁ : OneHighFamilyV2F1Ledger profile R)
    (f₂ : OneHighFamilyV2F2Ledger R profile)
    (f₃a : OneHighFamilyV2F3aLedger R profile)
    (f₃b : OneHighFamilyV2F3bLedger R profile)
    (hunsat : OneHighFamilyV2DimacsUnsat profile table) : False := by
  rcases oneHighFamilyV2Clauses_dimacsSatisfiable
    R profile hc f₁ f₂ f₃a f₃b with ⟨val, hval⟩
  rw [htable] at hval
  exact hunsat val hval

end Erdos85
