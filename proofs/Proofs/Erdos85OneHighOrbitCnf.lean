import Proofs.Erdos85OneHighFamilyCnfSatisfaction

/-!
# Table-pinned one-high CNFs

The wholesale family CNF existentially chooses every inter-branch miss count.
The successful sweep instead fixes those counts to one symmetric miss table.
This file defines that exact certificate-facing extension: its prefix is the
already certified PURE family formula, followed by one sequential-counter
equality for every non-mate unordered pair of branches.
-/

namespace Erdos85

/-- An encoder miss table.  Only entries with `c < j` and `j != c ^^^ 1`
are read by the pinned generator. -/
abbrev OneHighMissTable := Nat → Nat → Nat

/-- Non-mate unordered branch pairs, in the same nested-loop order as the
fleet worker (`c = 0..7`, then `j = 0..7`). -/
def oneHighFamilyTablePairs : List (Nat × Nat) :=
  (List.range 8).flatMap fun c =>
    (List.range 8).filterMap fun j =>
      if c < j ∧ j != (c ^^^ 1) then some (c, j) else none

theorem oneHighFamilyTablePairs_size : oneHighFamilyTablePairs.length = 24 := by
  native_decide

/-- The miss atoms in branch `c` pointing at branch `j`.  The matched-vertex
filter is precisely the worker's `if x in matched` list. -/
def oneHighFamilyTableMissAtoms (a c j : Nat) : List OneHighFamilyAtom :=
  (oneHighFamilyBlockVertices c).filterMap fun w =>
    if oneHighFamilyVertexMatched a w then some (.miss w j) else none

/-- Collect the identifiers of one table entry's miss atoms. -/
def oneHighFamilyTableMissVars (a c j : Nat)
    (st : OneHighFamilyGenState) : Array Int × OneHighFamilyGenState :=
  (oneHighFamilyTableMissAtoms a c j).foldl (fun (vars, st) atom =>
    let (id, st) := oneHighFamilyAtomId atom st
    (vars.push (id : Int), st)) (#[], st)

theorem oneHighFamilyIdsSound_tableMissVars
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a c j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyTableMissVars a c j st).2 := by
  unfold oneHighFamilyTableMissVars
  apply oneHighFamilyIdsSound_foldlAccum _ _ #[] h
  intro atom vars st hw
  exact oneHighFamilyIdsSound_atomId hw atom

/-- Append the exact-cardinality pin for one table entry. -/
def oneHighFamilyTablePairStep (a : Nat) (table : OneHighMissTable)
    (pair : Nat × Nat) (st : OneHighFamilyGenState) :
    OneHighFamilyGenState :=
  let (vars, st) := oneHighFamilyTableMissVars a pair.1 pair.2 st
  oneHighFamilyEqualsBlock vars (table pair.1 pair.2) st

theorem oneHighFamilyIdsSound_tablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyIdsSound (oneHighFamilyTablePairStep a table pair st) := by
  simp only [oneHighFamilyTablePairStep]
  exact oneHighFamilyIdsSound_equalsBlock
    (oneHighFamilyIdsSound_tableMissVars h a pair.1 pair.2) _ _

/-- The exact per-table CNF consumed by an orbit-sweep certificate. -/
def oneHighFamilyTableClauses (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyTablePairs
    (oneHighFamilyTablePairStep a table) (oneHighFamilyPureClauses a)

theorem oneHighFamilyIdsSound_tableClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyTableClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_pureClauses a)
    (fun pair st h => oneHighFamilyIdsSound_tablePairStep h a table pair)

/-! ## Semantic replay of the table suffix -/

noncomputable def oneHighFamilyCollectAtomVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom)
    (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (vars, acc) := input
  let (id, acc) := oneHighFamilyAtomIdVal R atom acc
  (vars.push (id : Int), acc)

theorem oneHighFamilyCollectAtomVal_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyInputAccumSound R input)
    (atom : OneHighFamilyAtom) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyCollectAtomVal R atom input) := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyCollectAtomVal]
  generalize hout : oneHighFamilyAtomIdVal R atom (st, val) = out
  rcases out with ⟨id, acc'⟩
  have hs := oneHighFamilyAtomIdVal_semanticSound R h.semantic atom
  rw [hout] at hs
  have hr := oneHighFamilyAtomIdVal_result R atom st val
  rw [hout] at hr
  dsimp at hr
  have hstate := oneHighFamilyAtomIdVal_state R atom st val
  rw [hout] at hstate
  have htop : st.top ≤ acc'.1.top := by
    rw [hstate]
    exact oneHighFamilyAtomId_top_le atom st
  constructor
  · exact hs
  · intro lit hlit
    simp only [Array.mem_push] at hlit
    rcases hlit with hold | rfl
    · exact h.nonzero lit hold
    · have hidPos := (hs.ids.id_bounds _ hr.1).1
      exact_mod_cast (Nat.ne_of_gt hidPos)
  · intro lit hlit
    simp only [Array.mem_push] at hlit
    rcases hlit with hold | rfl
    · exact (h.bounded lit hold).trans htop
    · simpa using (hs.ids.id_bounds _ hr.1).2

theorem oneHighFamilyCollectAtomsVal_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom)
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyInputAccumSound R input) :
    OneHighFamilyInputAccumSound R
      (atoms.foldl (fun input atom =>
        oneHighFamilyCollectAtomVal R atom input) input) := by
  induction atoms generalizing input with
  | nil => exact h
  | cons atom atoms ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyCollectAtomVal_sound R h atom)

structure OneHighFamilyCollectedAtomsMatch
    (atoms : List OneHighFamilyAtom)
    (input : Array Int × OneHighFamilyValState) where
  ids : List Nat
  vars_eq : input.1.toList = ids.map Int.ofNat
  aligned : List.Forall₂ (fun atom id =>
    (atom, id) ∈ input.2.1.ids) atoms ids

theorem oneHighFamilyCollectedAtomsMatch_length
    {atoms : List OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedAtomsMatch atoms input) :
    input.1.size = atoms.length := by
  have hv := congrArg List.length h.vars_eq
  have ha := h.aligned.length_eq
  simpa using hv.trans (by simpa using ha.symm)

theorem oneHighFamilyCollectedAtomsMatch_value
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atoms : List OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (hm : OneHighFamilyCollectedAtomsMatch atoms input)
    (hs : OneHighFamilySemanticSound R input.2)
    (i : Nat) (hi : i < input.1.size) :
    oneHighFamilyInputAccumRow input ⟨i, hi⟩ =
      oneHighFamilyAtomValue R (atoms.get ⟨i, by
        simpa [oneHighFamilyCollectedAtomsMatch_length hm] using hi⟩) := by
  have hiAtoms : i < atoms.length := by
    simpa [oneHighFamilyCollectedAtomsMatch_length hm] using hi
  have hiIds : i < hm.ids.length := by
    simpa using hm.aligned.length_eq ▸ hiAtoms
  have halign := hm.aligned.get hiAtoms hiIds
  have hiList : i < input.1.toList.length := by simpa using hi
  have hlistGet : input.1.toList[i] =
      (hm.ids.get ⟨i, hiIds⟩ : Int) := by
    have hg := List.get_of_eq hm.vars_eq ⟨i, hiList⟩
    rw [List.get_eq_getElem] at hg
    calc
      input.1.toList[i] =
          (hm.ids.map Int.ofNat)[i]'(by simpa using hiIds) := hg
      _ = (hm.ids[i]'hiIds : Int) := List.getElem_map _
      _ = (hm.ids.get ⟨i, hiIds⟩ : Int) := by rw [List.get_eq_getElem]
  have harrayGet : input.1.getD i 0 =
      (hm.ids.get ⟨i, hiIds⟩ : Int) := by
    rw [show input.1.getD i 0 = input.1[i] by simp [Array.getD, hi]]
    rw [← Array.getElem_toList hi]
    exact hlistGet
  unfold oneHighFamilyInputAccumRow oneHighFamilyLiteralRow
  rw [harrayGet]
  have hidPos := (hs.ids.id_bounds _ halign).1
  have hidPosInt : 0 < (hm.ids.get ⟨i, hiIds⟩ : Int) := by
    exact_mod_cast hidPos
  rw [dimacsLitValue, if_pos hidPosInt]
  exact hs.named _ _ halign

def oneHighFamilyCollectedAtomsMatch_empty
    (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedAtomsMatch [] (#[], acc) where
  ids := []
  vars_eq := rfl
  aligned := .nil

theorem oneHighFamilyCollectAtomVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyCollectAtomVal R atom input).2.1.ids := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyCollectAtomVal]
  exact oneHighFamilyAtomIdVal_old_mem R atom st val hmem

noncomputable def oneHighFamilyCollectedAtomsMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atoms : List OneHighFamilyAtom} {atom : OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedAtomsMatch atoms input) :
    OneHighFamilyCollectedAtomsMatch (atoms ++ [atom])
      (oneHighFamilyCollectAtomVal R atom input) := by
  rcases input with ⟨vars, acc⟩
  simp only [oneHighFamilyCollectAtomVal]
  generalize hout : oneHighFamilyAtomIdVal R atom acc = out
  rcases out with ⟨id, acc'⟩
  refine ⟨h.ids ++ [id], ?_, ?_⟩
  · rw [Array.toList_push, h.vars_eq]
    simp
  · have hold : List.Forall₂ (fun oldAtom oldId =>
        (oldAtom, oldId) ∈ acc'.1.ids) atoms h.ids := by
      apply h.aligned.imp
      intro oldAtom oldId hm
      have hx := oneHighFamilyAtomIdVal_old_mem R atom acc.1 acc.2 hm
      rw [hout] at hx
      exact hx
    have hnew := (oneHighFamilyAtomIdVal_result R atom acc.1 acc.2).1
    rw [hout] at hnew
    exact listForall₂_append_singleton hold hnew

noncomputable def oneHighFamilyCollectAtomsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  atoms.foldl (fun input atom =>
    oneHighFamilyCollectAtomVal R atom input) (#[], acc)

noncomputable def oneHighFamilyCollectAtomsVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedAtomsMatch atoms
      (oneHighFamilyCollectAtomsVal R atoms acc) := by
  unfold oneHighFamilyCollectAtomsVal
  induction atoms using List.reverseRecOn with
  | nil => exact oneHighFamilyCollectedAtomsMatch_empty acc
  | append_singleton atoms atom ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact oneHighFamilyCollectedAtomsMatch_push R ih

theorem oneHighFamilyCollectAtomVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom)
    (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyCollectAtomVal R atom input
    let raw :=
      let (id, st) := oneHighFamilyAtomId atom input.2.1
      (input.1.push (id : Int), st)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyCollectAtomVal]
  generalize hv : oneHighFamilyAtomIdVal R atom (st, val) = outVal
  rcases outVal with ⟨idVal, stVal, val'⟩
  generalize hs : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  have hid := oneHighFamilyAtomIdVal_id R atom st val
  have hstate := oneHighFamilyAtomIdVal_state R atom st val
  rw [hv, hs] at hid hstate
  exact ⟨by simp_all, by simp_all⟩

theorem oneHighFamilyCollectAtomsFoldVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom)
    (input : Array Int × OneHighFamilyValState) :
    let out := atoms.foldl (fun input atom =>
      oneHighFamilyCollectAtomVal R atom input) input
    let raw := atoms.foldl (fun (vars, st) atom =>
      let (id, st) := oneHighFamilyAtomId atom st
      (vars.push (id : Int), st)) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction atoms generalizing input with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyCollectAtomVal_projection R atom input
      have hi := ih (oneHighFamilyCollectAtomVal R atom input)
      rcases hp with ⟨hvars, hst⟩
      simpa [hvars, hst] using hi

theorem oneHighFamilyCollectAtomsVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atoms : List OneHighFamilyAtom) (acc : OneHighFamilyValState) :
    let out := oneHighFamilyCollectAtomsVal R atoms acc
    let raw := atoms.foldl (fun (vars, st) atom =>
      let (id, st) := oneHighFamilyAtomId atom st
      (vars.push (id : Int), st)) (#[], acc.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  exact oneHighFamilyCollectAtomsFoldVal_projection R atoms (#[], acc)

theorem oneHighFamilyCollectedAtoms_values
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atoms : List OneHighFamilyAtom}
    {input : Array Int × OneHighFamilyValState}
    (hm : OneHighFamilyCollectedAtomsMatch atoms input)
    (hs : OneHighFamilySemanticSound R input.2) :
    List.ofFn (oneHighFamilyInputAccumRow input) =
      atoms.map (oneHighFamilyAtomValue R) := by
  apply List.ext_getElem
  · simp [oneHighFamilyCollectedAtomsMatch_length hm]
  · intro i hiLeft hiRight
    have hi : i < input.1.size := by simpa using hiLeft
    have hv := oneHighFamilyCollectedAtomsMatch_value R hm hs i hi
    simpa [List.getElem_ofFn] using hv

/-- The exact miss table induced by a relabeled graph and a family profile. -/
noncomputable def oneHighFamilyGraphTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) : OneHighMissTable := fun c j =>
  ((oneHighFamilyTableMissAtoms a c j).map
    (oneHighFamilyAtomValue R)).count true

noncomputable def oneHighFamilyTablePairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let input := oneHighFamilyCollectAtomsVal R
    (oneHighFamilyTableMissAtoms a pair.1 pair.2) acc
  oneHighFamilyEqualsBlockVal input.1
    (oneHighFamilyInputAccumRow input) (table pair.1 pair.2) input.2

theorem oneHighFamilyTablePairStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (pair : Nat × Nat)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyTablePairStepVal R a
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

theorem oneHighFamilyTablePairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyTablePairStepVal R a table pair acc).1 =
      oneHighFamilyTablePairStep a table pair acc.1 := by
  unfold oneHighFamilyTablePairStepVal oneHighFamilyTablePairStep
  let atoms := oneHighFamilyTableMissAtoms a pair.1 pair.2
  let input := oneHighFamilyCollectAtomsVal R atoms acc
  have hp := oneHighFamilyCollectAtomsVal_projection R atoms acc
  change (oneHighFamilyEqualsBlockVal input.1
      (oneHighFamilyInputAccumRow input) (table pair.1 pair.2) input.2).1 = _
  rw [oneHighFamilyEqualsBlockVal_state]
  rcases hp with ⟨hvars, hstate⟩
  simp only [oneHighFamilyTableMissVars, atoms] at hvars hstate ⊢
  rw [hvars, hstate]

noncomputable def oneHighFamilyTableClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal oneHighFamilyTablePairs
    (oneHighFamilyTablePairStepVal R a (oneHighFamilyGraphTable R a))
    (oneHighFamilyPureClausesVal R a val)

theorem oneHighFamilyTableClausesVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyTableClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound R _ _
    (oneHighFamilyPureClausesVal_semanticSound a R hc val)
  intro pair acc hacc
  exact oneHighFamilyTablePairStepVal_semanticSound R a pair hacc

theorem oneHighFamilyTableClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyTableClausesVal R a val).1 =
      oneHighFamilyTableClauses a (oneHighFamilyGraphTable R a) := by
  unfold oneHighFamilyTableClausesVal oneHighFamilyTableClauses
  calc
    _ = oneHighFamilyRunList oneHighFamilyTablePairs
        (oneHighFamilyTablePairStep a (oneHighFamilyGraphTable R a))
        (oneHighFamilyPureClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyTablePairStepVal_state R a
          (oneHighFamilyGraphTable R a) pair acc)
    _ = _ := by rw [oneHighFamilyPureClausesVal_state]

/-- Every semantic family graph satisfies the table-pinned CNF belonging to
its induced miss table.  This is the graph-to-orbit-CNF composition socket. -/
theorem oneHighFamilyTableClauses_dimacsSatisfiable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val
        (oneHighFamilyTableClauses a
          (oneHighFamilyGraphTable R a)).clauses := by
  let initial : DimacsValuation := fun _ => false
  let out := oneHighFamilyTableClausesVal R a initial
  have hs := oneHighFamilyTableClausesVal_semanticSound R a hc initial
  have hstate := oneHighFamilyTableClausesVal_state R a initial
  refine ⟨out.2, ?_⟩
  rw [← hstate]
  exact hs.satisfied

def oneHighFamilyTableSatCnf (a : Nat) (table : OneHighMissTable) :
    Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (oneHighFamilyTableClauses a table).clauses

theorem oneHighFamilyTableSatCnf_sat_of_constraints
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (hc : OneHighPureFamilyCnfConstraints a R)
    (hnz : ∀ clause ∈ (oneHighFamilyTableClauses a
      (oneHighFamilyGraphTable R a)).clauses,
      DimacsClauseNonzero clause) :
    ∃ assignment : Nat → Bool,
      (oneHighFamilyTableSatCnf a
        (oneHighFamilyGraphTable R a)).Sat assignment := by
  rcases oneHighFamilyTableClauses_dimacsSatisfiable R a hc with ⟨val, hval⟩
  exact ⟨satAssignmentOfDimacs val,
    satCnf_of_dimacsFormulaSatisfied hval hnz⟩

end Erdos85
