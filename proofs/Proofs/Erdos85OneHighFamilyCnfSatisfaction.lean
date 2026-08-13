import Proofs.Erdos85OneHighFamilyCnfGenerator
import Proofs.Erdos85DimacsSatBridge

/-!
# Satisfaction adapter for the one-high family CNF

The generated DIMACS valuation has two layers.  Named `IDPool` atoms receive
their graph-semantic values here; sequential-counter auxiliaries are layered
above it by `seqCounterEqualsVal`.
-/

namespace Erdos85

def oneHighFamilyLookupId (id : Nat) :
    List (OneHighFamilyAtom × Nat) → Option OneHighFamilyAtom
  | [] => none
  | entry :: rest =>
      if entry.2 = id then some entry.1 else oneHighFamilyLookupId id rest

theorem oneHighFamilyLookupId_of_mem
    {atom : OneHighFamilyAtom} {id : Nat}
    {ids : List (OneHighFamilyAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    oneHighFamilyLookupId id ids = some atom := by
  induction ids with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hidFresh, hrest⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [oneHighFamilyLookupId]
      · have hne : entry.2 ≠ id := by
          intro heq
          apply hidFresh
          exact List.mem_map.mpr ⟨(atom, id), hmem, by simpa [heq]⟩
        simp [oneHighFamilyLookupId, hne, ih hrest hmem]

noncomputable def oneHighFamilyAtomValue (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] : OneHighFamilyAtom → Bool
  | .edge i j =>
      if hi : i < 40 then if hj : j < 40 then
        decide (R.Adj ⟨i, hi⟩ ⟨j, hj⟩) else false else false
  | .miss w b =>
      if hw : w < 40 then if hb : b < 8 then
        @decide (oneHighFamilyMissesBlock R ⟨w, hw⟩ ⟨b, hb⟩)
          (Classical.propDecidable _)
      else false else false
  | .midpoint x w z =>
      if hx : x < 40 then if hw : w < 40 then if hz : z < 40 then
        @decide (oneHighFamilyTAtom R ⟨x, hx⟩ ⟨w, hw⟩ ⟨z, hz⟩)
          (Classical.propDecidable _)
      else false else false else false
  | .common x z =>
      if hx : x < 40 then if hz : z < 40 then
        decide ((R.neighborFinset ⟨x, hx⟩ ∩
          R.neighborFinset ⟨z, hz⟩).card = 1)
      else false else false

noncomputable def oneHighFamilyNamedVal (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (ids : List (OneHighFamilyAtom × Nat)) :
    DimacsValuation := fun id =>
  match oneHighFamilyLookupId id ids with
  | some atom => oneHighFamilyAtomValue R atom
  | none => false

theorem oneHighFamilyNamedVal_of_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atom : OneHighFamilyAtom} {id : Nat}
    {ids : List (OneHighFamilyAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    oneHighFamilyNamedVal R ids id = oneHighFamilyAtomValue R atom := by
  rw [oneHighFamilyNamedVal, oneHighFamilyLookupId_of_mem hnodup hmem]

theorem oneHighFamilyPureNamedVal_of_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) {atom : OneHighFamilyAtom} {id : Nat}
    (hmem : (atom, id) ∈ (oneHighFamilyPureClauses a).ids) :
    oneHighFamilyNamedVal R (oneHighFamilyPureClauses a).ids id =
      oneHighFamilyAtomValue R atom := by
  exact oneHighFamilyNamedVal_of_mem R
    (oneHighFamilyIdsSound_pureClauses a).ids_nodup hmem

theorem oneHighFamilyPureNamedId_bounded
    (a : Nat) {atom : OneHighFamilyAtom} {id : Nat}
    (hmem : (atom, id) ∈ (oneHighFamilyPureClauses a).ids) :
    1 ≤ id ∧ id ≤ (oneHighFamilyPureClauses a).top :=
  (oneHighFamilyIdsSound_pureClauses a).id_bounds (atom, id) hmem

abbrev OneHighFamilyValState := OneHighFamilyGenState × DimacsValuation

def OneHighFamilyNamedValReifies
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (st : OneHighFamilyGenState) (val : DimacsValuation) : Prop :=
  ∀ atom id, (atom, id) ∈ st.ids →
    val id = oneHighFamilyAtomValue R atom

theorem oneHighFamilyNamedValReifies_initial
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (val : DimacsValuation) :
    OneHighFamilyNamedValReifies R {} val := by
  intro atom id hmem
  simp at hmem

/-- Semantic counterpart of `IDPool.id`: run the exact named allocation and
install the graph meaning at the returned identifier.  Reinstalling an
already-known atom is harmless and makes this usable uniformly in folds. -/
noncomputable def oneHighFamilyAtomIdVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) :
    StateM OneHighFamilyValState Nat := fun acc =>
  let (st, val) := acc
  let (id, st') := oneHighFamilyAtomId atom st
  (id, (st', Function.update val id (oneHighFamilyAtomValue R atom)))

noncomputable def oneHighFamilyEdgeIdVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) : StateM OneHighFamilyValState Nat :=
  oneHighFamilyAtomIdVal R (.edge (min i j) (max i j))

def oneHighFamilyEmitVal (clause : DimacsClause) :
    StateM OneHighFamilyValState Unit := fun acc =>
  let (st, val) := acc
  ((), ((oneHighFamilyEmit clause st).2, val))

/-- Semantic counterpart of a PySAT equality block.  Its state projection is
the byte-exact generator block, while its valuation projection installs the
canonical sequential-counter witnesses. -/
def oneHighFamilyEqualsBlockVal (vars : Array Int)
    (x : Fin vars.size → Bool) (bound : Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let (st, val) := acc
  (oneHighFamilyEqualsBlock vars bound st,
    seqCounterEqualsVal val st.top vars x bound)

@[simp] theorem oneHighFamilyAtomIdVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyAtomIdVal R atom (st, val)).2.1 =
      (oneHighFamilyAtomId atom st).2 := by
  generalize h : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [oneHighFamilyAtomIdVal, h]

@[simp] theorem oneHighFamilyAtomIdVal_value
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyAtomIdVal R atom (st, val)).2.2
        (oneHighFamilyAtomId atom st).1 =
      oneHighFamilyAtomValue R atom := by
  generalize h : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [oneHighFamilyAtomIdVal, h]

theorem oneHighFamilyAtomIdVal_reifies
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (hsound : OneHighFamilyIdsSound st)
    (hreifies : OneHighFamilyNamedValReifies R st val)
    (atom : OneHighFamilyAtom) :
    let out := oneHighFamilyAtomIdVal R atom (st, val)
    OneHighFamilyNamedValReifies R out.2.1 out.2.2 := by
  simp only [oneHighFamilyAtomIdVal]
  generalize hout : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  unfold oneHighFamilyAtomId at hout
  split at hout
  next _ hlookup =>
    cases hout
    intro atom' id' hmem
    have hatomMem : (atom, id) ∈ st.ids :=
      oneHighFamilyLookup_eq_some_mem hlookup
    by_cases hid : id' = id
    · subst id'
      have hlookupAtom := oneHighFamilyLookupId_of_mem
        hsound.ids_nodup hatomMem
      have hlookupAtom' := oneHighFamilyLookupId_of_mem
        hsound.ids_nodup hmem
      have hatom : atom' = atom := by
        rw [hlookupAtom] at hlookupAtom'
        exact Option.some.inj hlookupAtom'.symm
      subst atom'
      simp
    · simp [Function.update, hid, hreifies atom' id' hmem]
  next hlookup =>
    cases hout
    intro atom' id' hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hnew | hold
    · cases hnew
      simp
    · have hbound := hsound.id_bounds (atom', id') hold
      have hne : id' ≠ st.top + 1 := by omega
      simp [Function.update, hne, hreifies atom' id' hold]

@[simp] theorem oneHighFamilyEmitVal_state
    (clause : DimacsClause) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyEmitVal clause (st, val)).2.1 =
      (oneHighFamilyEmit clause st).2 := by
  simp [oneHighFamilyEmitVal]

@[simp] theorem oneHighFamilyEmitVal_value
    (clause : DimacsClause) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyEmitVal clause (st, val)).2.2 = val := by
  simp [oneHighFamilyEmitVal]

theorem oneHighFamilyEmitVal_reifies
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (hreifies : OneHighFamilyNamedValReifies R st val)
    (clause : DimacsClause) :
    let out := oneHighFamilyEmitVal clause (st, val)
    OneHighFamilyNamedValReifies R out.2.1 out.2.2 := by
  dsimp [oneHighFamilyEmitVal, OneHighFamilyNamedValReifies]
  intro atom id hmem
  exact hreifies atom id hmem

@[simp] theorem oneHighFamilyEqualsBlockVal_state
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat)
    (st : OneHighFamilyGenState) (val : DimacsValuation) :
    (oneHighFamilyEqualsBlockVal vars x bound (st, val)).1 =
      oneHighFamilyEqualsBlock vars bound st := by
  simp [oneHighFamilyEqualsBlockVal]

theorem oneHighFamilyEqualsBlockVal_reifies
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (hsound : OneHighFamilyIdsSound st)
    (hreifies : OneHighFamilyNamedValReifies R st val)
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat) :
    let out := oneHighFamilyEqualsBlockVal vars x bound (st, val)
    OneHighFamilyNamedValReifies R out.1 out.2 := by
  dsimp [oneHighFamilyEqualsBlockVal]
  intro atom id hmem
  have hmem' : (atom, id) ∈ st.ids := by
    exact hmem
  have hid := (hsound.id_bounds (atom, id) hmem').2
  exact (seqCounterEqualsVal_input val st.top vars x bound id hid).trans
    (hreifies atom id hmem')

/-- Induction package carried by the semantic replay of the family generator:
named IDs are well formed and reified, while every clause emitted so far is
satisfied and bounded by the current global top. -/
structure OneHighFamilySemanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (acc : OneHighFamilyValState) : Prop where
  ids : OneHighFamilyIdsSound acc.1
  named : OneHighFamilyNamedValReifies R acc.1 acc.2
  satisfied : dimacsFormulaSatisfied acc.2 acc.1.clauses
  bounded : dimacsFormulaBounded acc.1.top acc.1.clauses

theorem oneHighFamilySemanticSound_initial
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (({} : OneHighFamilyGenState), val) where
  ids := oneHighFamilyIdsSound_initial
  named := oneHighFamilyNamedValReifies_initial R val
  satisfied := dimacsFormulaSatisfied_empty val
  bounded := dimacsFormulaBounded_empty 0

theorem oneHighFamilyAtomIdVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (atom : OneHighFamilyAtom) :
    OneHighFamilySemanticSound R
      (oneHighFamilyAtomIdVal R atom (st, val)).2 := by
  simp only [oneHighFamilyAtomIdVal]
  generalize hout : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  unfold oneHighFamilyAtomId at hout
  split at hout
  next _ hlookup =>
    cases hout
    have hmem : (atom, id) ∈ st.ids :=
      oneHighFamilyLookup_eq_some_mem hlookup
    have hvalue : val id = oneHighFamilyAtomValue R atom :=
      h.named atom id hmem
    have hvalEq : Function.update val id
        (oneHighFamilyAtomValue R atom) = val := by
      funext k
      by_cases hk : k = id
      · subst k
        simp [hvalue]
      · simp [Function.update, hk]
    simpa [hvalEq] using h
  next hlookup =>
    cases hout
    let nextVal := Function.update val (st.top + 1)
      (oneHighFamilyAtomValue R atom)
    have hagree : ∀ id, id ≤ st.top → val id = nextVal id := by
      intro id hid
      have hne : id ≠ st.top + 1 := by omega
      simp [nextVal, hne]
    have hsat : dimacsFormulaSatisfied nextVal st.clauses :=
      dimacsFormulaSatisfied_of_bounded_agree h.satisfied h.bounded hagree
    constructor
    · simpa [oneHighFamilyAtomId, hlookup] using
        oneHighFamilyIdsSound_atomId h.ids atom
    · simpa [oneHighFamilyAtomIdVal, oneHighFamilyAtomId, hlookup] using
        oneHighFamilyAtomIdVal_reifies R h.ids h.named atom
    · exact hsat
    · exact dimacsFormulaBounded_mono (Nat.le_succ st.top) h.bounded

theorem oneHighFamilyEmitVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (clause : DimacsClause)
    (hclauseSat : dimacsClauseSatisfied val clause)
    (hclauseBound : dimacsClauseBounded st.top clause) :
    OneHighFamilySemanticSound R
      (oneHighFamilyEmitVal clause (st, val)).2 := by
  constructor
  · exact oneHighFamilyIdsSound_emit h.ids clause
  · exact oneHighFamilyEmitVal_reifies R h.named clause
  · intro candidate hc
    change candidate ∈ st.clauses.push clause at hc
    simp only [Array.mem_push] at hc
    rcases hc with hc | rfl
    · exact h.satisfied candidate hc
    · exact hclauseSat
  · intro candidate hc
    change candidate ∈ st.clauses.push clause at hc
    simp only [Array.mem_push] at hc
    rcases hc with hc | rfl
    · exact h.bounded candidate hc
    · exact hclauseBound

theorem oneHighFamilyEqualsBlockVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat)
    (hinput : SeqCounterInputReifies val st.top vars x)
    (hcount : seqPrefixTrue x vars.size = bound) :
    OneHighFamilySemanticSound R
      (oneHighFamilyEqualsBlockVal vars x bound (st, val)) := by
  let hblock := seqCounterEqualsVal_formulaSatisfied_append
    val st.top st.clauses vars x h.satisfied h.bounded hinput bound hcount
  constructor
  · exact oneHighFamilyIdsSound_equalsBlock h.ids vars bound
  · exact oneHighFamilyEqualsBlockVal_reifies R h.ids h.named vars x bound
  · simpa [oneHighFamilyEqualsBlockVal, oneHighFamilyEqualsBlock] using hblock.1
  · simpa [oneHighFamilyEqualsBlockVal, oneHighFamilyEqualsBlock] using hblock.2.1

end Erdos85
