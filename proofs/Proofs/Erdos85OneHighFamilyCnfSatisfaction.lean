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
  | .saver x w =>
      if hx : x < 40 then if hw : w < 40 then
        if hb : (x / 5 ^^^ 1) < 8 then
        decide (R.Adj ⟨x, hx⟩ ⟨w, hw⟩) &&
          @decide (oneHighFamilyMissesBlock R ⟨w, hw⟩
            ⟨(x / 5 ^^^ 1), hb⟩) (Classical.propDecidable _)
        else false else false else false

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

def oneHighFamilyRunListVal {α : Type} (xs : List α)
    (step : α → OneHighFamilyValState → OneHighFamilyValState)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  xs.foldl (fun acc x => step x acc) acc

theorem oneHighFamilyRunListVal_state {α : Type} (xs : List α)
    (stepVal : α → OneHighFamilyValState → OneHighFamilyValState)
    (step : α → OneHighFamilyGenState → OneHighFamilyGenState)
    (acc : OneHighFamilyValState)
    (hstep : ∀ x acc, (stepVal x acc).1 = step x acc.1) :
    (oneHighFamilyRunListVal xs stepVal acc).1 =
      oneHighFamilyRunList xs step acc.1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [oneHighFamilyRunListVal, oneHighFamilyRunList,
        List.foldl_cons]
      calc
        _ = oneHighFamilyRunList xs step (stepVal x acc).1 :=
          ih (stepVal x acc)
        _ = oneHighFamilyRunList xs step (step x acc.1) := by
          rw [hstep x acc]

@[simp] theorem oneHighFamilyAtomIdVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyAtomIdVal R atom (st, val)).2.1 =
      (oneHighFamilyAtomId atom st).2 := by
  generalize h : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [oneHighFamilyAtomIdVal, h]

@[simp] theorem oneHighFamilyAtomIdVal_id
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyAtomIdVal R atom (st, val)).1 =
      (oneHighFamilyAtomId atom st).1 := by
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

theorem oneHighFamilyAtomIdVal_result
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    let out := oneHighFamilyAtomIdVal R atom (st, val)
    (atom, out.1) ∈ out.2.1.ids ∧
      out.2.2 out.1 = oneHighFamilyAtomValue R atom := by
  generalize h : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  constructor
  · simpa [oneHighFamilyAtomIdVal, h] using
      oneHighFamilyAtomId_mem atom st
  · simp [oneHighFamilyAtomIdVal, h]

theorem oneHighFamilyAtomIdVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState)
    (val : DimacsValuation) {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ st.ids) :
    let out := oneHighFamilyAtomIdVal R atom (st, val)
    entry ∈ out.2.1.ids := by
  generalize h : oneHighFamilyAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simpa [oneHighFamilyAtomIdVal, h] using
    oneHighFamilyAtomId_ids_subset atom st entry hmem

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

theorem oneHighFamilyAtomId_positive
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (atom : OneHighFamilyAtom) :
    0 < (oneHighFamilyAtomId atom st).1 := by
  let out := oneHighFamilyAtomId atom st
  have hs := oneHighFamilyIdsSound_atomId h atom
  have hm := oneHighFamilyAtomId_mem atom st
  exact (hs.id_bounds (atom, out.1) (by simpa [out] using hm)).1

theorem oneHighFamilyAtomId_bounded
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (atom : OneHighFamilyAtom) :
    (oneHighFamilyAtomId atom st).1 ≤ (oneHighFamilyAtomId atom st).2.top := by
  let out := oneHighFamilyAtomId atom st
  have hs := oneHighFamilyIdsSound_atomId h atom
  have hm := oneHighFamilyAtomId_mem atom st
  exact (hs.id_bounds (atom, out.1) (by simpa [out] using hm)).2

theorem dimacsClauseSatisfied_singleton_positive
    {val : DimacsValuation} {id : Nat} (hid : 0 < id)
    (hvalue : val id = true) :
    dimacsClauseSatisfied val [(id : Int)] := by
  refine ⟨(id : Int), by simp, ?_⟩
  simp [dimacsLitValue, hid, hvalue]

theorem dimacsClauseSatisfied_singleton_negative
    {val : DimacsValuation} {id : Nat}
    (hvalue : val id = false) :
    dimacsClauseSatisfied val [-(id : Int)] := by
  refine ⟨-(id : Int), by simp, ?_⟩
  simp [dimacsLitValue, hvalue]

theorem dimacsClauseBounded_singleton_positive
    {top id : Nat} (hid : id ≤ top) :
    dimacsClauseBounded top [(id : Int)] := by
  intro lit hlit
  simp at hlit
  simpa [hlit] using hid

theorem dimacsClauseBounded_singleton_negative
    {top id : Nat} (hid : id ≤ top) :
    dimacsClauseBounded top [-(id : Int)] := by
  intro lit hlit
  simp at hlit
  simpa [hlit] using hid

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

theorem dimacsClauseSatisfied_negative_pair
    {val : DimacsValuation} {a b : Nat}
    (hnot : ¬(val a = true ∧ val b = true)) :
    dimacsClauseSatisfied val [-(a : Int), -(b : Int)] := by
  cases ha : val a
  · refine ⟨-(a : Int), by simp, ?_⟩
    simp [dimacsLitValue, ha]
  · have hb : val b = false := by
      cases hb' : val b
      · rfl
      · exact False.elim (hnot ⟨ha, hb'⟩)
    refine ⟨-(b : Int), by simp, ?_⟩
    simp [dimacsLitValue, hb]

theorem dimacsClauseBounded_negative_pair
    {top a b : Nat} (ha : a ≤ top) (hb : b ≤ top) :
    dimacsClauseBounded top [-(a : Int), -(b : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl
  · simpa using ha
  · simpa using hb

theorem dimacsClauseSatisfied_negative_four
    {val : DimacsValuation} {a b c d : Nat}
    (hnot : ¬(val a = true ∧ val b = true ∧
      val c = true ∧ val d = true)) :
    dimacsClauseSatisfied val
      [-(a : Int), -(b : Int), -(c : Int), -(d : Int)] := by
  cases ha : val a
  · exact ⟨-(a : Int), by simp, by simp [dimacsLitValue, ha]⟩
  · cases hb : val b
    · exact ⟨-(b : Int), by simp, by simp [dimacsLitValue, hb]⟩
    · cases hc : val c
      · exact ⟨-(c : Int), by simp, by simp [dimacsLitValue, hc]⟩
      · have hd : val d = false := by
          cases hd' : val d
          · rfl
          · exact False.elim (hnot ⟨ha, hb, hc, hd'⟩)
        exact ⟨-(d : Int), by simp, by simp [dimacsLitValue, hd]⟩

theorem dimacsClauseBounded_negative_four
    {top a b c d : Nat} (ha : a ≤ top) (hb : b ≤ top)
    (hc : c ≤ top) (hd : d ≤ top) :
    dimacsClauseBounded top
      [-(a : Int), -(b : Int), -(c : Int), -(d : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl | rfl | rfl
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

theorem dimacsClauseSatisfied_positive_ids
    {val : DimacsValuation} {a : Nat} {ids : List Nat}
    (haPos : 0 < a) (hidsPos : ∀ id ∈ ids, 0 < id)
    (h : val a = true ∨ ∃ id ∈ ids, val id = true) :
    dimacsClauseSatisfied val
      ((a : Int) :: List.map (fun id : Nat => (id : Int)) ids) := by
  rcases h with ha | ⟨id, hid, hval⟩
  · refine ⟨(a : Int), by simp, ?_⟩
    simp [dimacsLitValue, ha, haPos]
  · refine ⟨(id : Int), by simp [hid], ?_⟩
    simp [dimacsLitValue, hval, hidsPos id hid]

theorem dimacsClauseBounded_positive_ids
    {top a : Nat} {ids : List Nat}
    (ha : a ≤ top) (hids : ∀ id ∈ ids, id ≤ top) :
    dimacsClauseBounded top
      ((a : Int) :: List.map (fun id : Nat => (id : Int)) ids) := by
  intro lit hlit
  simp only [List.mem_cons] at hlit
  rcases hlit with rfl | hlit
  · simpa using ha
  · obtain ⟨id, hid, heq⟩ := List.mem_map.mp hlit
    rw [← heq]
    simpa using hids id hid

theorem dimacsClauseSatisfied_negative_positive
    {val : DimacsValuation} {a b : Nat} (hbPos : 0 < b)
    (himp : val a = true → val b = true) :
    dimacsClauseSatisfied val [-(a : Int), (b : Int)] := by
  cases ha : val a
  · exact ⟨-(a : Int), by simp, by simp [dimacsLitValue, ha]⟩
  · refine ⟨(b : Int), by simp, ?_⟩
    simp [dimacsLitValue, hbPos, himp ha]

theorem dimacsClauseBounded_negative_positive
    {top a b : Nat} (ha : a ≤ top) (hb : b ≤ top) :
    dimacsClauseBounded top [-(a : Int), (b : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl
  · simpa using ha
  · simpa using hb

theorem dimacsClauseSatisfied_positive_negative_pair
    {val : DimacsValuation} {a b c : Nat} (haPos : 0 < a)
    (himp : val b = true → val c = true → val a = true) :
    dimacsClauseSatisfied val
      [(a : Int), -(b : Int), -(c : Int)] := by
  cases hb : val b
  · exact ⟨-(b : Int), by simp, by simp [dimacsLitValue, hb]⟩
  · cases hc : val c
    · exact ⟨-(c : Int), by simp, by simp [dimacsLitValue, hc]⟩
    · refine ⟨(a : Int), by simp, ?_⟩
      simp [dimacsLitValue, haPos, himp hb hc]

theorem dimacsClauseBounded_positive_negative_pair
    {top a b c : Nat} (ha : a ≤ top) (hb : b ≤ top) (hc : c ≤ top) :
    dimacsClauseBounded top [(a : Int), -(b : Int), -(c : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl | rfl
  · simpa using ha
  · simpa using hb
  · simpa using hc

theorem dimacsClauseSatisfied_negative_positive_ids
    {val : DimacsValuation} {c : Nat} {ids : List Nat}
    (hcPos : 0 < c) (hidsPos : ∀ id ∈ ids, 0 < id)
    (himp : val c = true → ∃ id ∈ ids, val id = true) :
    dimacsClauseSatisfied val
      (-(c : Int) :: List.map (fun id : Nat => (id : Int)) ids) := by
  cases hc : val c
  · refine ⟨-(c : Int), by simp, ?_⟩
    simp [dimacsLitValue, hc, hcPos]
  · rcases himp hc with ⟨id, hid, hval⟩
    refine ⟨(id : Int), by simp [hid], ?_⟩
    simp [dimacsLitValue, hval, hidsPos id hid]

theorem dimacsClauseBounded_negative_positive_ids
    {top c : Nat} {ids : List Nat}
    (hc : c ≤ top) (hids : ∀ id ∈ ids, id ≤ top) :
    dimacsClauseBounded top
      (-(c : Int) :: List.map (fun id : Nat => (id : Int)) ids) := by
  intro lit hlit
  simp only [List.mem_cons] at hlit
  rcases hlit with rfl | hlit
  · simpa using hc
  · rcases List.mem_map.mp hlit with ⟨id, hid, rfl⟩
    simpa using hids id hid

noncomputable def oneHighFamilyFourNegativeAtomsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom₁ atom₂ atom₃ atom₄ : OneHighFamilyAtom)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let (id₁, acc) := oneHighFamilyAtomIdVal R atom₁ acc
  let (id₂, acc) := oneHighFamilyAtomIdVal R atom₂ acc
  let (id₃, acc) := oneHighFamilyAtomIdVal R atom₃ acc
  let (id₄, acc) := oneHighFamilyAtomIdVal R atom₄ acc
  (oneHighFamilyEmitVal
    [-(id₁ : Int), -(id₂ : Int), -(id₃ : Int), -(id₄ : Int)] acc).2

theorem oneHighFamilyFourNegativeAtomsVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom₁ atom₂ atom₃ atom₄ : OneHighFamilyAtom)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyFourNegativeAtomsVal R atom₁ atom₂ atom₃ atom₄ acc).1 =
      let (id₁, st) := oneHighFamilyAtomId atom₁ acc.1
      let (id₂, st) := oneHighFamilyAtomId atom₂ st
      let (id₃, st) := oneHighFamilyAtomId atom₃ st
      let (id₄, st) := oneHighFamilyAtomId atom₄ st
      (oneHighFamilyEmit
        [-(id₁ : Int), -(id₂ : Int), -(id₃ : Int), -(id₄ : Int)] st).2 := by
  generalize h₁ : oneHighFamilyAtomId atom₁ acc.1 = out₁
  rcases out₁ with ⟨id₁, st₁⟩
  generalize h₂ : oneHighFamilyAtomId atom₂ st₁ = out₂
  rcases out₂ with ⟨id₂, st₂⟩
  generalize h₃ : oneHighFamilyAtomId atom₃ st₂ = out₃
  rcases out₃ with ⟨id₃, st₃⟩
  generalize h₄ : oneHighFamilyAtomId atom₄ st₃ = out₄
  rcases out₄ with ⟨id₄, st₄⟩
  simp [oneHighFamilyFourNegativeAtomsVal, oneHighFamilyAtomIdVal,
    oneHighFamilyEmitVal, h₁, h₂, h₃, h₄]

theorem oneHighFamilyFourNegativeAtomsVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (atom₁ atom₂ atom₃ atom₄ : OneHighFamilyAtom)
    (hnot : ¬(oneHighFamilyAtomValue R atom₁ = true ∧
      oneHighFamilyAtomValue R atom₂ = true ∧
      oneHighFamilyAtomValue R atom₃ = true ∧
      oneHighFamilyAtomValue R atom₄ = true)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyFourNegativeAtomsVal R atom₁ atom₂ atom₃ atom₄ acc) := by
  simp only [oneHighFamilyFourNegativeAtomsVal]
  generalize h₁ : oneHighFamilyAtomIdVal R atom₁ acc = out₁
  rcases out₁ with ⟨id₁, acc₁⟩
  have hs₁ := oneHighFamilyAtomIdVal_semanticSound R h atom₁
  rw [h₁] at hs₁
  have hr₁ := oneHighFamilyAtomIdVal_result R atom₁ acc.1 acc.2
  rw [h₁] at hr₁
  dsimp at hr₁
  generalize h₂ : oneHighFamilyAtomIdVal R atom₂ acc₁ = out₂
  rcases out₂ with ⟨id₂, acc₂⟩
  have hs₂ := oneHighFamilyAtomIdVal_semanticSound R hs₁ atom₂
  rw [h₂] at hs₂
  have hr₂ := oneHighFamilyAtomIdVal_result R atom₂ acc₁.1 acc₁.2
  rw [h₂] at hr₂
  dsimp at hr₂
  generalize h₃ : oneHighFamilyAtomIdVal R atom₃ acc₂ = out₃
  rcases out₃ with ⟨id₃, acc₃⟩
  have hs₃ := oneHighFamilyAtomIdVal_semanticSound R hs₂ atom₃
  rw [h₃] at hs₃
  have hr₃ := oneHighFamilyAtomIdVal_result R atom₃ acc₂.1 acc₂.2
  rw [h₃] at hr₃
  dsimp at hr₃
  generalize h₄ : oneHighFamilyAtomIdVal R atom₄ acc₃ = out₄
  rcases out₄ with ⟨id₄, acc₄⟩
  have hs₄ := oneHighFamilyAtomIdVal_semanticSound R hs₃ atom₄
  rw [h₄] at hs₄
  have hr₄ := oneHighFamilyAtomIdVal_result R atom₄ acc₃.1 acc₃.2
  rw [h₄] at hr₄
  dsimp at hr₄
  have lift₂ {entry : OneHighFamilyAtom × Nat}
      (hm : entry ∈ acc₁.1.ids) : entry ∈ acc₂.1.ids := by
    have hx := oneHighFamilyAtomIdVal_old_mem R atom₂
      acc₁.1 acc₁.2 hm
    rw [h₂] at hx
    exact hx
  have lift₃ {entry : OneHighFamilyAtom × Nat}
      (hm : entry ∈ acc₂.1.ids) : entry ∈ acc₃.1.ids := by
    have hx := oneHighFamilyAtomIdVal_old_mem R atom₃
      acc₂.1 acc₂.2 hm
    rw [h₃] at hx
    exact hx
  have lift₄ {entry : OneHighFamilyAtom × Nat}
      (hm : entry ∈ acc₃.1.ids) : entry ∈ acc₄.1.ids := by
    have hx := oneHighFamilyAtomIdVal_old_mem R atom₄
      acc₃.1 acc₃.2 hm
    rw [h₄] at hx
    exact hx
  have hm₁ := lift₄ (lift₃ (lift₂ hr₁.1))
  have hm₂ := lift₄ (lift₃ hr₂.1)
  have hm₃ := lift₄ hr₃.1
  have hvalues : ¬(acc₄.2 id₁ = true ∧ acc₄.2 id₂ = true ∧
      acc₄.2 id₃ = true ∧ acc₄.2 id₄ = true) := by
    rw [hs₄.named atom₁ id₁ hm₁, hs₄.named atom₂ id₂ hm₂,
      hs₄.named atom₃ id₃ hm₃, hr₄.2]
    exact hnot
  simp only [h₂, h₃, h₄]
  apply oneHighFamilyEmitVal_semanticSound R hs₄
  · exact dimacsClauseSatisfied_negative_four hvalues
  · exact dimacsClauseBounded_negative_four
      (hs₄.ids.id_bounds _ hm₁).2
      (hs₄.ids.id_bounds _ hm₂).2
      (hs₄.ids.id_bounds _ hm₃).2
      (hs₄.ids.id_bounds _ hr₄.1).2

noncomputable def oneHighFamilyEdgeUnitVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (present : Bool)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let (id, acc) := oneHighFamilyEdgeIdVal R i j acc
  (oneHighFamilyEmitVal
    [if present then (id : Int) else -(id : Int)] acc).2

theorem oneHighFamilyEdgeUnitVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (present : Bool) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyEdgeUnitVal R i j present (st, val)).1 =
      let (id, st) := oneHighFamilyEdgeId i j st
      (oneHighFamilyEmit
        [if present then (id : Int) else -(id : Int)] st).2 := by
  generalize halloc : oneHighFamilyAtomId
    (.edge (min i j) (max i j)) st = out
  rcases out with ⟨id, st'⟩
  simp [oneHighFamilyEdgeUnitVal, oneHighFamilyEdgeIdVal,
    oneHighFamilyAtomIdVal, oneHighFamilyEdgeId, oneHighFamilyEmitVal,
    halloc]

noncomputable def oneHighFamilyInternalPairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a b i j : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyValState :=
  let twoEdges := ¬(b % 2 = 0 ∧ b / 2 < a)
  let present := decide ((i = 0 ∧ j = 1) ∨
    (twoEdges ∧ i = 2 ∧ j = 3))
  oneHighFamilyEdgeUnitVal R (5 * b + i) (5 * b + j) present acc

theorem oneHighFamilyInternalPairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a b i j : Nat) (st : OneHighFamilyGenState)
    (val : DimacsValuation) :
    (oneHighFamilyInternalPairStepVal R a b i j (st, val)).1 =
      oneHighFamilyInternalPairStep a b i j st := by
  rw [oneHighFamilyInternalPairStepVal]
  rw [oneHighFamilyEdgeUnitVal_state]
  have hparity : (b % 2 = 1 ∨ a ≤ b / 2) =
      (b % 2 = 0 → a ≤ b / 2) := by
    apply propext
    omega
  simp [oneHighFamilyInternalPairStep, hparity]
  rfl

theorem oneHighFamilyEdgeUnitVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (i j : Nat) (present : Bool)
    (hvalue : oneHighFamilyAtomValue R
      (.edge (min i j) (max i j)) = present) :
    OneHighFamilySemanticSound R
      (oneHighFamilyEdgeUnitVal R i j present (st, val)) := by
  simp only [oneHighFamilyEdgeUnitVal, oneHighFamilyEdgeIdVal]
  generalize hout : oneHighFamilyAtomIdVal R
    (.edge (min i j) (max i j)) (st, val) = out
  rcases out with ⟨id, acc⟩
  have hatom := oneHighFamilyAtomIdVal_semanticSound R h
    (.edge (min i j) (max i j))
  rw [hout] at hatom
  have houtId : id = (oneHighFamilyAtomId
      (.edge (min i j) (max i j)) st).1 := by
    have heq := oneHighFamilyAtomIdVal_id R
      (.edge (min i j) (max i j)) st val
    rw [hout] at heq
    exact heq
  have houtState : acc.1 = (oneHighFamilyAtomId
      (.edge (min i j) (max i j)) st).2 := by
    have heq := oneHighFamilyAtomIdVal_state R
      (.edge (min i j) (max i j)) st val
    rw [hout] at heq
    exact heq
  have hm : ((.edge (min i j) (max i j)), id) ∈ acc.1.ids := by
    rw [houtId, houtState]
    exact oneHighFamilyAtomId_mem _ st
  have hb := hatom.ids.id_bounds _ hm
  have hval : acc.2 id = present :=
    (hatom.named _ id hm).trans hvalue
  apply oneHighFamilyEmitVal_semanticSound R hatom
  · cases present
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact dimacsClauseSatisfied_singleton_negative hval
    · simp only [↓reduceIte]
      exact dimacsClauseSatisfied_singleton_positive hb.1 hval
  · cases present <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact dimacsClauseBounded_singleton_negative hb.2
    · exact dimacsClauseBounded_singleton_positive hb.2

theorem oneHighFamilyInternalPairStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {st : OneHighFamilyGenState} {val : DimacsValuation}
    (h : OneHighFamilySemanticSound R (st, val))
    (a b i j : Nat)
    (hvalue : oneHighFamilyAtomValue R
      (.edge (min (5 * b + i) (5 * b + j))
        (max (5 * b + i) (5 * b + j))) =
      decide ((i = 0 ∧ j = 1) ∨
        (¬(b % 2 = 0 ∧ b / 2 < a) ∧ i = 2 ∧ j = 3))) :
    OneHighFamilySemanticSound R
      (oneHighFamilyInternalPairStepVal R a b i j (st, val)) := by
  exact oneHighFamilyEdgeUnitVal_semanticSound R h _ _ _ hvalue

theorem oneHighFamilyInternalPair_edgeValue
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {b i j : Nat} (hb : b < 8) (hi : i < 5) (hj : j < 5)
    (hij : i < j) :
    oneHighFamilyAtomValue R
      (.edge (min (5 * b + i) (5 * b + j))
        (max (5 * b + i) (5 * b + j))) =
      decide ((i = 0 ∧ j = 1) ∨
        (¬(b % 2 = 0 ∧ b / 2 < a) ∧ i = 2 ∧ j = 3)) := by
  have hui : 5 * b + i < 40 := by omega
  have huj : 5 * b + j < 40 := by omega
  let u : Fin 40 := ⟨5 * b + i, hui⟩
  let v : Fin 40 := ⟨5 * b + j, huj⟩
  have hblock : Fin.divNat (m := 8) (n := 5) u =
      Fin.divNat (m := 8) (n := 5) v := by
    apply Fin.ext
    simp [u, v, Fin.divNat, Nat.mul_add_div, Nat.div_eq_of_lt hi,
      Nat.div_eq_of_lt hj]
  have hcanonical := hc.relation.1 u v hblock
  have hmin : min (5 * b + i) (5 * b + j) = 5 * b + i :=
    min_eq_left (by omega)
  have hmax : max (5 * b + i) (5 * b + j) = 5 * b + j :=
    max_eq_right (by omega)
  have hcanonical' : decide (R.Adj u v) =
      decide ((i = 0 ∧ j = 1) ∨
        (¬(b % 2 = 0 ∧ b / 2 < a) ∧ i = 2 ∧ j = 3)) := by
    rw [hcanonical]
    apply Bool.decide_congr
    simp [oneHighFamilyTwoEdges,
      u, v, Fin.divNat, Fin.modNat, Nat.mul_add_div,
      Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj,
      Fin.ext_iff]
    omega
  simpa [oneHighFamilyAtomValue, hmin, hmax, hui, huj, u, v] using
    hcanonical'

theorem oneHighFamilyRunListVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {α : Type} (xs : List α)
    (step : α → OneHighFamilyValState → OneHighFamilyValState)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hstep : ∀ x acc, OneHighFamilySemanticSound R acc →
      OneHighFamilySemanticSound R (step x acc)) :
    OneHighFamilySemanticSound R (oneHighFamilyRunListVal xs step acc) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih =>
      simp only [oneHighFamilyRunListVal, List.foldl_cons]
      exact ih (hstep x acc h)

theorem oneHighFamilyRunListVal_semanticSound_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {α : Type} (xs : List α)
    (step : α → OneHighFamilyValState → OneHighFamilyValState)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hstep : ∀ x, x ∈ xs → ∀ acc, OneHighFamilySemanticSound R acc →
      OneHighFamilySemanticSound R (step x acc)) :
    OneHighFamilySemanticSound R (oneHighFamilyRunListVal xs step acc) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih =>
      simp only [oneHighFamilyRunListVal, List.foldl_cons]
      apply ih (hstep x (by simp) acc h)
      intro y hy acc hacc
      exact hstep y (by simp [hy]) acc hacc

noncomputable def oneHighFamilyInternalBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a b : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 5) (fun i acc =>
    oneHighFamilyRunListVal (List.range 5) (fun j acc =>
      if i < j then oneHighFamilyInternalPairStepVal R a b i j acc else acc)
      acc) acc

theorem oneHighFamilyInternalBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {b : Nat} (hb : b < 8) :
    OneHighFamilySemanticSound R
      (oneHighFamilyInternalBlockStepVal R a b acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro i hi acc hiSound
  have hi' : i < 5 := List.mem_range.mp hi
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hiSound
  intro j hj acc hjSound
  have hj' : j < 5 := List.mem_range.mp hj
  split
  next hij =>
    exact oneHighFamilyInternalPairStepVal_semanticSound R hjSound a b i j
      (oneHighFamilyInternalPair_edgeValue a R hc hb hi' hj' hij)
  next => exact hjSound

theorem oneHighFamilyInternalBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a b : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyInternalBlockStepVal R a b acc).1 =
      oneHighFamilyInternalBlockStep a b acc.1 := by
  unfold oneHighFamilyInternalBlockStepVal oneHighFamilyInternalBlockStep
  apply oneHighFamilyRunListVal_state
  intro i acc
  apply oneHighFamilyRunListVal_state
  intro j acc
  split
  · exact oneHighFamilyInternalPairStepVal_state R a b i j acc.1 acc.2
  · rfl

noncomputable def oneHighFamilyInternalUnitsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 8)
    (oneHighFamilyInternalBlockStepVal R a)
    (({} : OneHighFamilyGenState), val)

theorem oneHighFamilyInternalUnitsVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyInternalUnitsVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilySemanticSound_initial R val)
  intro b hb acc hacc
  exact oneHighFamilyInternalBlockStepVal_semanticSound a R hc hacc
    (List.mem_range.mp hb)

theorem oneHighFamilyInternalUnitsVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyInternalUnitsVal R a val).1 =
      oneHighFamilyInternalUnits a := by
  unfold oneHighFamilyInternalUnitsVal oneHighFamilyInternalUnits
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun b acc => oneHighFamilyInternalBlockStepVal_state R a b acc)

noncomputable def oneHighFamilyMatePairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b i j : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyEdgeUnitVal R (5 * b + i) (5 * (b + 1) + j) false acc

theorem oneHighFamilyMatePairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b i j : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyMatePairStepVal R b i j acc).1 =
      oneHighFamilyMatePairStep b i j acc.1 := by
  rw [oneHighFamilyMatePairStepVal, oneHighFamilyEdgeUnitVal_state]
  rfl

theorem oneHighFamilyMatePair_edgeValue
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {b i j : Nat} (hb : b + 1 < 8) (hi : i < 5) (hj : j < 5)
    (hmate : oneHighStandardMate (⟨b, by omega⟩ : Fin 8) =
      (⟨b + 1, hb⟩ : Fin 8)) :
    oneHighFamilyAtomValue R
      (.edge (min (5 * b + i) (5 * (b + 1) + j))
        (max (5 * b + i) (5 * (b + 1) + j))) = false := by
  have hui : 5 * b + i < 40 := by omega
  have huj : 5 * (b + 1) + j < 40 := by omega
  let u : Fin 40 := ⟨5 * b + i, hui⟩
  let v : Fin 40 := ⟨5 * (b + 1) + j, huj⟩
  have hmateBlocks : Fin.divNat (m := 8) (n := 5) v =
      oneHighStandardMate (Fin.divNat (m := 8) (n := 5) u) := by
    rw [show Fin.divNat (m := 8) (n := 5) u =
      (⟨b, by omega⟩ : Fin 8) by
        apply Fin.ext
        simp [u, Fin.divNat, Nat.mul_add_div, Nat.div_eq_of_lt hi]]
    rw [hmate]
    apply Fin.ext
    simp [v, Fin.divNat, Nat.mul_add_div, Nat.div_eq_of_lt hj]
  have hnotAdj := hc.relation.2.1 u v hmateBlocks
  have hmin : min (5 * b + i) (5 * (b + 1) + j) = 5 * b + i :=
    min_eq_left (by omega)
  have hmax : max (5 * b + i) (5 * (b + 1) + j) =
      5 * (b + 1) + j := max_eq_right (by omega)
  simp [oneHighFamilyAtomValue, hmin, hmax, hui, huj, u, v,
    hnotAdj]

theorem oneHighFamilyAtomValue_edge
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {i j : Nat} (hi : i < 40) (hj : j < 40) :
    oneHighFamilyAtomValue R (.edge (min i j) (max i j)) =
      decide (R.Adj (⟨i, hi⟩ : Fin 40) ⟨j, hj⟩) := by
  by_cases hij : i ≤ j
  · have hmin : min i j = i := min_eq_left hij
    have hmax : max i j = j := max_eq_right hij
    simp [oneHighFamilyAtomValue, hmin, hmax, hi, hj]
  · have hji : j ≤ i := by omega
    have hmin : min i j = j := min_eq_right hji
    have hmax : max i j = i := max_eq_left hji
    simp [oneHighFamilyAtomValue, hmin, hmax, hi, hj, R.adj_comm]

theorem oneHighFamilyMatePairStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {b i j : Nat} (hb : b + 1 < 8) (hi : i < 5) (hj : j < 5)
    (hmate : oneHighStandardMate (⟨b, by omega⟩ : Fin 8) =
      (⟨b + 1, hb⟩ : Fin 8)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMatePairStepVal R b i j acc) := by
  exact oneHighFamilyEdgeUnitVal_semanticSound R h _ _ false
    (oneHighFamilyMatePair_edgeValue a R hc hb hi hj hmate)

noncomputable def oneHighFamilyMateBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 5) (fun i acc =>
    oneHighFamilyRunListVal (List.range 5)
      (fun j acc => oneHighFamilyMatePairStepVal R b i j acc) acc) acc

theorem oneHighFamilyMateBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {b : Nat} (hb : b + 1 < 8)
    (hmate : oneHighStandardMate (⟨b, by omega⟩ : Fin 8) =
      (⟨b + 1, hb⟩ : Fin 8)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMateBlockStepVal R b acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro i hi acc hiSound
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hiSound
  intro j hj acc hjSound
  exact oneHighFamilyMatePairStepVal_semanticSound a R hc hjSound hb
    (List.mem_range.mp hi) (List.mem_range.mp hj) hmate

theorem oneHighFamilyMateBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyMateBlockStepVal R b acc).1 =
      oneHighFamilyMateBlockStep b acc.1 := by
  unfold oneHighFamilyMateBlockStepVal oneHighFamilyMateBlockStep
  apply oneHighFamilyRunListVal_state
  intro i acc
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun j acc => oneHighFamilyMatePairStepVal_state R b i j acc)

noncomputable def oneHighFamilyBaseUnitsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal [0, 2, 4, 6]
    (oneHighFamilyMateBlockStepVal R) (oneHighFamilyInternalUnitsVal R a val)

theorem oneHighFamilyBaseUnitsVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (oneHighFamilyBaseUnitsVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyInternalUnitsVal_semanticSound a R hc val)
  intro b hb acc hacc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 0) (by omega) (by decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 2) (by omega) (by decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 4) (by omega) (by decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 6) (by omega) (by decide)

theorem oneHighFamilyBaseUnitsVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyBaseUnitsVal R a val).1 = oneHighFamilyBaseUnits a := by
  unfold oneHighFamilyBaseUnitsVal oneHighFamilyBaseUnits
  calc
    _ = oneHighFamilyRunList [0, 2, 4, 6] oneHighFamilyMateBlockStep
        (oneHighFamilyInternalUnitsVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun b acc => oneHighFamilyMateBlockStepVal_state R b acc)
    _ = _ := by rw [oneHighFamilyInternalUnitsVal_state]

noncomputable def oneHighFamilyC4SameMidpointStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j w : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let (eiw, acc) := oneHighFamilyEdgeIdVal R i w acc
  let (ejw, acc) := oneHighFamilyEdgeIdVal R j w acc
  (oneHighFamilyEmitVal [-(eiw : Int), -(ejw : Int)] acc).2

theorem oneHighFamilyC4SameMidpointStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j w : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4SameMidpointStepVal R i j w acc).1 =
      oneHighFamilyC4SameMidpointStep i j w acc.1 := by
  generalize h₁ : oneHighFamilyAtomId
    (.edge (min i w) (max i w)) acc.1 = out₁
  rcases out₁ with ⟨eiw, st₁⟩
  generalize h₂ : oneHighFamilyAtomId
    (.edge (min j w) (max j w)) st₁ = out₂
  rcases out₂ with ⟨ejw, st₂⟩
  simp [oneHighFamilyC4SameMidpointStepVal, oneHighFamilyEdgeIdVal,
    oneHighFamilyAtomIdVal, oneHighFamilyEmitVal,
    oneHighFamilyC4SameMidpointStep, oneHighFamilyEdgeId, h₁, h₂]

theorem oneHighFamilyC4SameMidpointStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i j w : Nat} (hi : i < 40) (hj : j < 40) (hw : w < 40)
    (hij : i ≠ j)
    (hblock : Fin.divNat (m := 8) (n := 5) (⟨i, hi⟩ : Fin 40) =
      Fin.divNat (m := 8) (n := 5) (⟨j, hj⟩ : Fin 40)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4SameMidpointStepVal R i j w acc) := by
  simp only [oneHighFamilyC4SameMidpointStepVal, oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R
    (.edge (min i w) (max i w)) acc = out₁
  rcases out₁ with ⟨eiw, acc₁⟩
  have hs₁ := oneHighFamilyAtomIdVal_semanticSound R h
    (.edge (min i w) (max i w))
  rw [h₁] at hs₁
  have hr₁ := oneHighFamilyAtomIdVal_result R
    (.edge (min i w) (max i w)) acc.1 acc.2
  rw [h₁] at hr₁
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min j w) (max j w)) acc₁ = out₂
  rcases out₂ with ⟨ejw, acc₂⟩
  have hs₂ := oneHighFamilyAtomIdVal_semanticSound R hs₁
    (.edge (min j w) (max j w))
  rw [h₂] at hs₂
  have hr₂ := oneHighFamilyAtomIdVal_result R
    (.edge (min j w) (max j w)) acc₁.1 acc₁.2
  rw [h₂] at hr₂
  dsimp at hr₁ hr₂
  have hstate₂ := oneHighFamilyAtomIdVal_state R
    (.edge (min j w) (max j w)) acc₁.1 acc₁.2
  rw [h₂] at hstate₂
  have hm₁ : ((.edge (min i w) (max i w)), eiw) ∈ acc₂.1.ids := by
    rw [hstate₂]
    exact oneHighFamilyAtomId_ids_subset _ acc₁.1 _ hr₁.1
  have hei : acc₂.2 eiw = decide
      (R.Adj (⟨i, hi⟩ : Fin 40) ⟨w, hw⟩) := by
    exact (hs₂.named _ eiw hm₁).trans (oneHighFamilyAtomValue_edge R hi hw)
  have hej : acc₂.2 ejw = decide
      (R.Adj (⟨j, hj⟩ : Fin 40) ⟨w, hw⟩) :=
    hr₂.2.trans (oneHighFamilyAtomValue_edge R hj hw)
  have hnot : ¬(acc₂.2 eiw = true ∧ acc₂.2 ejw = true) := by
    rw [hei, hej]
    simp only [decide_eq_true_eq]
    intro hadj
    have hzero := hc.relation.2.2.2.1
      (⟨i, hi⟩ : Fin 40) ⟨j, hj⟩ (by exact Fin.ne_of_val_ne hij)
      hblock
    have hwmem : (⟨w, hw⟩ : Fin 40) ∈
        R.neighborFinset ⟨i, hi⟩ ∩ R.neighborFinset ⟨j, hj⟩ := by
      simp [SimpleGraph.mem_neighborFinset, hadj.1, hadj.2]
    have hpos := Finset.card_pos.mpr ⟨_, hwmem⟩
    omega
  simp only [h₂]
  apply oneHighFamilyEmitVal_semanticSound R hs₂
  · exact dimacsClauseSatisfied_negative_pair hnot
  · exact dimacsClauseBounded_negative_pair
      (hs₂.ids.id_bounds _ hm₁).2
      (hs₂.ids.id_bounds _ hr₂.1).2

noncomputable def oneHighFamilyC4SamePairVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (oneHighFamilyOtherVertices i j)
    (fun w acc => oneHighFamilyC4SameMidpointStepVal R i j w acc) acc

theorem oneHighFamilyC4SamePairVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i j : Nat} (hi : i < 40) (hj : j < 40) (hij : i ≠ j)
    (hblockNat : i / 5 = j / 5) :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4SamePairVal R i j acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro w hwmem acc hwSound
  have hw : w < 40 := by
    simp only [oneHighFamilyOtherVertices, List.mem_filter,
      List.mem_range] at hwmem
    exact hwmem.1
  have hblock : Fin.divNat (m := 8) (n := 5) (⟨i, hi⟩ : Fin 40) =
      Fin.divNat (m := 8) (n := 5) (⟨j, hj⟩ : Fin 40) := by
    apply Fin.ext
    exact hblockNat
  exact oneHighFamilyC4SameMidpointStepVal_semanticSound
    a R hc hwSound hi hj hw hij hblock

theorem oneHighFamilyC4SamePairVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4SamePairVal R i j acc).1 =
      oneHighFamilyRunList (oneHighFamilyOtherVertices i j)
        (fun w st => oneHighFamilyC4SameMidpointStep i j w st) acc.1 := by
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun w acc => oneHighFamilyC4SameMidpointStepVal_state R i j w acc)

noncomputable def oneHighFamilyC4CrossMidpointsStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j w w' : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyFourNegativeAtomsVal R
    (.edge (min i w) (max i w)) (.edge (min j w) (max j w))
    (.edge (min i w') (max i w')) (.edge (min j w') (max j w')) acc

theorem oneHighFamilyC4CrossMidpointsStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j w w' : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4CrossMidpointsStepVal R i j w w' acc).1 =
      oneHighFamilyC4CrossMidpointsStep i j w w' acc.1 := by
  rw [oneHighFamilyC4CrossMidpointsStepVal]
  rw [oneHighFamilyFourNegativeAtomsVal_state]
  rfl

theorem oneHighFamilyC4CrossMidpointsStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i j w w' : Nat} (hi : i < 40) (hj : j < 40)
    (hw : w < 40) (hw' : w' < 40) (hij : i ≠ j) (hww' : w ≠ w') :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4CrossMidpointsStepVal R i j w w' acc) := by
  apply oneHighFamilyFourNegativeAtomsVal_semanticSound R h
  intro hall
  rw [oneHighFamilyAtomValue_edge R hi hw,
    oneHighFamilyAtomValue_edge R hj hw,
    oneHighFamilyAtomValue_edge R hi hw',
    oneHighFamilyAtomValue_edge R hj hw'] at hall
  simp only [decide_eq_true_eq] at hall
  let I := R.neighborFinset (⟨i, hi⟩ : Fin 40) ∩
    R.neighborFinset (⟨j, hj⟩ : Fin 40)
  have hwmem : (⟨w, hw⟩ : Fin 40) ∈ I := by
    simp [I, SimpleGraph.mem_neighborFinset, hall.1, hall.2.1]
  have hw'mem : (⟨w', hw'⟩ : Fin 40) ∈ I := by
    simp [I, SimpleGraph.mem_neighborFinset, hall.2.2.1, hall.2.2.2]
  have hfinNe : (⟨w, hw⟩ : Fin 40) ≠ ⟨w', hw'⟩ :=
    Fin.ne_of_val_ne hww'
  have hsubset : ({(⟨w, hw⟩ : Fin 40), ⟨w', hw'⟩} : Finset (Fin 40)) ⊆ I := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hwmem
    · exact hw'mem
  have htwo : 2 ≤ I.card := by
    have hle := Finset.card_le_card hsubset
    simpa [Finset.card_pair hfinNe] using hle
  have hone := hc.relation.2.2.1
    (⟨i, hi⟩ : Fin 40) ⟨j, hj⟩ (Fin.ne_of_val_ne hij)
  change I.card ≤ 1 at hone
  omega

noncomputable def oneHighFamilyC4CrossPairVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let others := oneHighFamilyOtherVertices i j
  oneHighFamilyRunListVal others (fun w acc =>
    oneHighFamilyRunListVal others (fun w' acc =>
      if w < w' then
        oneHighFamilyC4CrossMidpointsStepVal R i j w w' acc
      else acc) acc) acc

theorem oneHighFamilyC4CrossPairVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i j : Nat} (hi : i < 40) (hj : j < 40) (hij : i ≠ j) :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4CrossPairVal R i j acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro w hwmem acc hwSound
  have hw : w < 40 := by
    simp only [oneHighFamilyOtherVertices, List.mem_filter,
      List.mem_range] at hwmem
    exact hwmem.1
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hwSound
  intro w' hw'mem acc hw'Sound
  have hw' : w' < 40 := by
    simp only [oneHighFamilyOtherVertices, List.mem_filter,
      List.mem_range] at hw'mem
    exact hw'mem.1
  split
  next hww' =>
    exact oneHighFamilyC4CrossMidpointsStepVal_semanticSound
      a R hc hw'Sound hi hj hw hw' hij (by omega)
  next => exact hw'Sound

theorem oneHighFamilyC4CrossPairVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4CrossPairVal R i j acc).1 =
      let others := oneHighFamilyOtherVertices i j
      oneHighFamilyRunList others (fun w st =>
        oneHighFamilyRunList others (fun w' st =>
          if w < w' then
            oneHighFamilyC4CrossMidpointsStep i j w w' st
          else st) st) acc.1 := by
  unfold oneHighFamilyC4CrossPairVal
  apply oneHighFamilyRunListVal_state
  intro w acc
  apply oneHighFamilyRunListVal_state
  intro w' acc
  split
  · exact oneHighFamilyC4CrossMidpointsStepVal_state R i j w w' acc
  · rfl

noncomputable def oneHighFamilyC4PairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  if i / 5 = j / 5 then oneHighFamilyC4SamePairVal R i j acc
  else oneHighFamilyC4CrossPairVal R i j acc

theorem oneHighFamilyC4PairStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i j : Nat} (hi : i < 40) (hj : j < 40) (hij : i ≠ j) :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4PairStepVal R i j acc) := by
  unfold oneHighFamilyC4PairStepVal
  split
  next hblock =>
    exact oneHighFamilyC4SamePairVal_semanticSound
      a R hc h hi hj hij hblock
  next =>
    exact oneHighFamilyC4CrossPairVal_semanticSound
      a R hc h hi hj hij

theorem oneHighFamilyC4PairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i j : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4PairStepVal R i j acc).1 =
      oneHighFamilyC4PairStep i j acc.1 := by
  unfold oneHighFamilyC4PairStepVal oneHighFamilyC4PairStep
  split
  · exact oneHighFamilyC4SamePairVal_state R i j acc
  · exact oneHighFamilyC4CrossPairVal_state R i j acc

noncomputable def oneHighFamilyC4OuterStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40) (fun j acc =>
    if i < j then oneHighFamilyC4PairStepVal R i j acc else acc) acc

theorem oneHighFamilyC4OuterStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {i : Nat} (hi : i < 40) :
    OneHighFamilySemanticSound R
      (oneHighFamilyC4OuterStepVal R i acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro j hj acc hjSound
  have hj' := List.mem_range.mp hj
  split
  next hij =>
    exact oneHighFamilyC4PairStepVal_semanticSound
      a R hc hjSound hi hj' (by omega)
  next =>
    exact hjSound

theorem oneHighFamilyC4OuterStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (i : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyC4OuterStepVal R i acc).1 =
      oneHighFamilyC4OuterStep i acc.1 := by
  unfold oneHighFamilyC4OuterStepVal oneHighFamilyC4OuterStep
  apply oneHighFamilyRunListVal_state
  intro j acc
  split
  · exact oneHighFamilyC4PairStepVal_state R i j acc
  · rfl

noncomputable def oneHighFamilyC4ClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40) (oneHighFamilyC4OuterStepVal R)
    (oneHighFamilyBaseUnitsVal R a val)

theorem oneHighFamilyC4ClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (oneHighFamilyC4ClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyBaseUnitsVal_semanticSound a R hc val)
  intro i hi acc hacc
  exact oneHighFamilyC4OuterStepVal_semanticSound
    a R hc hacc (List.mem_range.mp hi)

theorem oneHighFamilyC4ClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyC4ClausesVal R a val).1 = oneHighFamilyC4Clauses a := by
  unfold oneHighFamilyC4ClausesVal oneHighFamilyC4Clauses
  calc
    _ = oneHighFamilyRunList (List.range 40) oneHighFamilyC4OuterStep
        (oneHighFamilyBaseUnitsVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun i acc => oneHighFamilyC4OuterStepVal_state R i acc)
    _ = _ := by rw [oneHighFamilyBaseUnitsVal_state]

noncomputable def oneHighFamilyAtMostOnePairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y x x' : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyC4SameMidpointStepVal R x x' y acc

theorem oneHighFamilyAtMostOnePairStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {y x x' : Nat} (hy : y < 40) (hx : x < 40) (hx' : x' < 40)
    (hxx' : x ≠ x') (hblockNat : x / 5 = x' / 5) :
    OneHighFamilySemanticSound R
      (oneHighFamilyAtMostOnePairStepVal R y x x' acc) := by
  exact oneHighFamilyC4SameMidpointStepVal_semanticSound
    a R hc h hx hx' hy hxx' (by
      apply Fin.ext
      exact hblockNat)

theorem oneHighFamilyAtMostOnePairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y x x' : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyAtMostOnePairStepVal R y x x' acc).1 =
      oneHighFamilyAtMostOnePairStep y x x' acc.1 := by
  rw [oneHighFamilyAtMostOnePairStepVal,
    oneHighFamilyC4SameMidpointStepVal_state]
  simp [oneHighFamilyC4SameMidpointStep,
    oneHighFamilyAtMostOnePairStep, oneHighFamilyEdgeId,
    min_comm, max_comm]

noncomputable def oneHighFamilyAtMostOneVertexStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b y : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  if y / 5 = b ^^^ 1 then acc else
    let xs := (oneHighFamilyBlockVertices b).filter fun x => x ≠ y
    oneHighFamilyRunListVal xs (fun x acc =>
      oneHighFamilyRunListVal xs (fun x' acc =>
        if x < x' then oneHighFamilyAtMostOnePairStepVal R y x x' acc
        else acc) acc) acc

theorem oneHighFamilyBlockVertices_mem
    {b x : Nat} (hb : b < 8) (hx : x ∈ oneHighFamilyBlockVertices b) :
    x < 40 ∧ x / 5 = b := by
  simp only [oneHighFamilyBlockVertices, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have hr' := List.mem_range.mp hr
  constructor
  · omega
  · simp [Nat.mul_add_div, Nat.div_eq_of_lt hr']

theorem oneHighFamilyVertex_val (b : Fin 8) (r : Fin 5) :
    (oneHighFamilyVertex b r).val = 5 * b.val + r.val := by
  simp [oneHighFamilyVertex, finProdFinEquiv]
  omega

theorem oneHighFamilyVertex_mem_blockVertices (b : Fin 8) (r : Fin 5) :
    (oneHighFamilyVertex b r).val ∈ oneHighFamilyBlockVertices b.val := by
  rw [oneHighFamilyVertex_val]
  simp [oneHighFamilyBlockVertices]

theorem oneHighFamilyMissesBlock_iff_blockVertices
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {w b : Nat} (hw : w < 40) (hb : b < 8) :
    oneHighFamilyMissesBlock R (⟨w, hw⟩ : Fin 40) ⟨b, hb⟩ ↔
      ∀ (z : Nat) (hz : z ∈ oneHighFamilyBlockVertices b),
        ¬ R.Adj (⟨w, hw⟩ : Fin 40)
          ⟨z, (oneHighFamilyBlockVertices_mem hb hz).1⟩ := by
  constructor
  · intro hmiss z hz
    simp only [oneHighFamilyBlockVertices, List.mem_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    have hr5 := List.mem_range.mp hr
    have hv : oneHighFamilyVertex (⟨b, hb⟩ : Fin 8) (⟨r, hr5⟩ : Fin 5) =
        (⟨5 * b + r, by omega⟩ : Fin 40) := by
      apply Fin.ext
      exact oneHighFamilyVertex_val _ _
    rw [← hv]
    exact hmiss (⟨r, hr5⟩ : Fin 5)
  · intro h r
    have hz := oneHighFamilyVertex_mem_blockVertices (⟨b, hb⟩ : Fin 8) r
    have hn := h (oneHighFamilyVertex (⟨b, hb⟩ : Fin 8) r).val hz
    simpa using hn

theorem oneHighFamilyAtMostOneVertexStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {b y : Nat} (hb : b < 8) (hy : y < 40) :
    OneHighFamilySemanticSound R
      (oneHighFamilyAtMostOneVertexStepVal R b y acc) := by
  unfold oneHighFamilyAtMostOneVertexStepVal
  split
  next => exact h
  next =>
    apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
    intro x hxmem acc hxSound
    have hxbase := (List.mem_filter.mp hxmem).1
    have hx := oneHighFamilyBlockVertices_mem hb hxbase
    apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hxSound
    intro x' hx'mem acc hx'Sound
    have hx'base := (List.mem_filter.mp hx'mem).1
    have hx' := oneHighFamilyBlockVertices_mem hb hx'base
    split
    next hxx' =>
      exact oneHighFamilyAtMostOnePairStepVal_semanticSound
        a R hc hx'Sound hy hx.1 hx'.1 (by omega) (hx.2.trans hx'.2.symm)
    next => exact hx'Sound

theorem oneHighFamilyAtMostOneVertexStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b y : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyAtMostOneVertexStepVal R b y acc).1 =
      oneHighFamilyAtMostOneVertexStep b y acc.1 := by
  unfold oneHighFamilyAtMostOneVertexStepVal
  unfold oneHighFamilyAtMostOneVertexStep
  split
  · rfl
  · apply oneHighFamilyRunListVal_state
    intro x acc
    apply oneHighFamilyRunListVal_state
    intro x' acc
    split
    · exact oneHighFamilyAtMostOnePairStepVal_state R y x x' acc
    · rfl

noncomputable def oneHighFamilyAtMostOneBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40)
    (oneHighFamilyAtMostOneVertexStepVal R b) acc

theorem oneHighFamilyAtMostOneBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    {b : Nat} (hb : b < 8) :
    OneHighFamilySemanticSound R
      (oneHighFamilyAtMostOneBlockStepVal R b acc) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ h
  intro y hy acc hySound
  exact oneHighFamilyAtMostOneVertexStepVal_semanticSound
    a R hc hySound hb (List.mem_range.mp hy)

theorem oneHighFamilyAtMostOneBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (b : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyAtMostOneBlockStepVal R b acc).1 =
      oneHighFamilyAtMostOneBlockStep b acc.1 := by
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun y acc => oneHighFamilyAtMostOneVertexStepVal_state R b y acc)

noncomputable def oneHighFamilyAtMostOneBlockClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 8)
    (oneHighFamilyAtMostOneBlockStepVal R)
    (oneHighFamilyC4ClausesVal R a val)

theorem oneHighFamilyAtMostOneBlockClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyAtMostOneBlockClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyC4ClausesVal_semanticSound a R hc val)
  intro b hb acc hacc
  exact oneHighFamilyAtMostOneBlockStepVal_semanticSound
    a R hc hacc (List.mem_range.mp hb)

theorem oneHighFamilyAtMostOneBlockClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyAtMostOneBlockClausesVal R a val).1 =
      oneHighFamilyAtMostOneBlockClauses a := by
  unfold oneHighFamilyAtMostOneBlockClausesVal
  unfold oneHighFamilyAtMostOneBlockClauses
  calc
    _ = oneHighFamilyRunList (List.range 8) oneHighFamilyAtMostOneBlockStep
        (oneHighFamilyC4ClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun b acc => oneHighFamilyAtMostOneBlockStepVal_state R b acc)
    _ = _ := by rw [oneHighFamilyC4ClausesVal_state]

def oneHighFamilyLiteralRow (val : DimacsValuation) (vars : Array Int) :
    Fin vars.size → Bool := fun i => dimacsLitValue val (vars.getD i.val 0)

theorem seqPrefixTrue_oneHighFamilyLiteralRow
    (val : DimacsValuation) (vars : Array Int) :
    seqPrefixTrue (oneHighFamilyLiteralRow val vars) vars.size =
      ((Finset.range vars.size).filter fun i =>
        dimacsLitValue val (vars.getD i 0)).card := by
  unfold seqPrefixTrue oneHighFamilyLiteralRow
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hi : i < vars.size
  · simp [hi]
  · simp [hi]

def finsetRangeFilterEquivFinSubtype (n : Nat) (p : Fin n → Prop)
    [DecidablePred p] :
    {i // i ∈ (Finset.range n).filter fun k =>
      if hk : k < n then p ⟨k, hk⟩ else false} ≃
      {i : Fin n // p i} where
  toFun i := ⟨⟨i.1, Finset.mem_range.mp (Finset.mem_filter.mp i.2).1⟩, by
    simpa [Finset.mem_range.mp (Finset.mem_filter.mp i.2).1] using
      (Finset.mem_filter.mp i.2).2⟩
  invFun i := ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.1.2, by
    simp [i.1.2, i.2]⟩⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

theorem finsetRangeFilter_card_eq_finSubtype_card
    (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    ((Finset.range n).filter fun k =>
      if hk : k < n then p ⟨k, hk⟩ else false).card =
      Fintype.card {i : Fin n // p i} := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (finsetRangeFilterEquivFinSubtype n p)

theorem oneHighStandardMate_val_eq_xor (b : Fin 8) :
    (oneHighStandardMate b).val = b.val ^^^ 1 := by
  decide +revert

theorem oneHighFamilyFarDegreeBound_eq
    (a y : Nat) (hy : y < 40) :
    oneHighFamilyFarDegreeBound a y =
      oneHighFamilyFarDegree a
        (Fin.divNat (m := 8) (n := 5) (⟨y, hy⟩ : Fin 40))
        (Fin.modNat (m := 8) (n := 5) (⟨y, hy⟩ : Fin 40)) := by
  simp [oneHighFamilyFarDegreeBound, oneHighFamilyFarDegree,
    oneHighFamilyInternalEdges, Fin.divNat, Fin.modNat]

theorem oneHighFamilyFarVertices_mem_iff
    {y x : Nat} (hy : y < 40) :
    x ∈ oneHighFamilyFarVertices y ↔
      x < 40 ∧ x ≠ y ∧ x / 5 ≠ y / 5 ∧
        x / 5 ≠ (oneHighStandardMate
          (Fin.divNat (m := 8) (n := 5) (⟨y, hy⟩ : Fin 40))).val := by
  rw [oneHighFamilyFarVertices]
  simp only [List.mem_filter, List.mem_range]
  rw [oneHighStandardMate_val_eq_xor]
  simp [Fin.divNat]

structure OneHighFamilyInputAccumSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (input : Array Int × OneHighFamilyValState) : Prop where
  semantic : OneHighFamilySemanticSound R input.2
  nonzero : ∀ lit ∈ input.1, lit ≠ 0
  bounded : ∀ lit ∈ input.1, lit.natAbs ≤ input.2.1.top

theorem oneHighFamilyInputAccumSound_empty
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc) :
    OneHighFamilyInputAccumSound R (#[], acc) where
  semantic := h
  nonzero := by simp
  bounded := by simp

theorem oneHighFamilyAtomId_top_le
    (atom : OneHighFamilyAtom) (st : OneHighFamilyGenState) :
    st.top ≤ (oneHighFamilyAtomId atom st).2.top := by
  unfold oneHighFamilyAtomId
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ _

noncomputable def oneHighFamilyCollectEdgeVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y x : Nat) (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (vars, acc) := input
  let (id, acc) := oneHighFamilyEdgeIdVal R y x acc
  (vars.push (id : Int), acc)

structure OneHighFamilyCollectedEdgesMatch
    (y : Nat) (xs : List Nat)
    (input : Array Int × OneHighFamilyValState) where
  ids : List Nat
  vars_eq : input.1.toList = List.map (fun id : Nat => Int.ofNat id) ids
  aligned : List.Forall₂ (fun x id =>
    ((.edge (min y x) (max y x)), id) ∈ input.2.1.ids) xs ids

def oneHighFamilyCollectedEdgesMatch_empty
    (y : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedEdgesMatch y [] (#[], acc) where
  ids := []
  vars_eq := rfl
  aligned := .nil

theorem listForall₂_append_singleton {α β : Type*}
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) {x : α} {y : β} (hxy : r x y) :
    List.Forall₂ r (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons hxy .nil
  | cons hab hrest ih => exact .cons hab ih

theorem listForall₂_exists_right_of_mem {α β : Type*}
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, r x y := by
  induction h with
  | nil => simp at hx
  | @cons a b as bs hab hrest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b, by simp, hab⟩
      · rcases ih hx with ⟨y, hy, hr⟩
        exact ⟨y, by simp [hy], hr⟩

theorem listForall₂_exists_left_of_mem {α β : Type*}
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, r x y := by
  induction h with
  | nil => simp at hy
  | @cons a b as bs hab hrest ih =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨a, by simp, hab⟩
      · rcases ih hy with ⟨x, hx, hr⟩
        exact ⟨x, by simp [hx], hr⟩

noncomputable def oneHighFamilyCollectedEdgesMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y x : Nat} {xs : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedEdgesMatch y xs input) :
    OneHighFamilyCollectedEdgesMatch y (xs ++ [x])
      (oneHighFamilyCollectEdgeVal R y x input) := by
  rcases input with ⟨vars, acc⟩
  simp only [oneHighFamilyCollectEdgeVal, oneHighFamilyEdgeIdVal]
  generalize hout : oneHighFamilyAtomIdVal R
    (.edge (min y x) (max y x)) acc = out
  rcases out with ⟨id, acc'⟩
  refine ⟨h.ids ++ [id], ?_, ?_⟩
  · rw [Array.toList_push, h.vars_eq]
    simp
  · have hold : List.Forall₂ (fun z oldId =>
        ((.edge (min y z) (max y z)), oldId) ∈ acc'.1.ids) xs h.ids := by
      apply h.aligned.imp
      intro z oldId hm
      have hx := oneHighFamilyAtomIdVal_old_mem R
        (.edge (min y x) (max y x)) acc.1 acc.2 hm
      rw [hout] at hx
      exact hx
    have hnew := (oneHighFamilyAtomIdVal_result R
      (.edge (min y x) (max y x)) acc.1 acc.2).1
    rw [hout] at hnew
    exact listForall₂_append_singleton hold hnew

theorem oneHighFamilyCollectEdgeVal_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyInputAccumSound R input)
    (y x : Nat) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyCollectEdgeVal R y x input) := by
  rcases input with ⟨vars, acc⟩
  rcases acc with ⟨st, val⟩
  simp only [oneHighFamilyCollectEdgeVal, oneHighFamilyEdgeIdVal]
  generalize hout : oneHighFamilyAtomIdVal R
    (.edge (min y x) (max y x)) (st, val) = out
  rcases out with ⟨id, acc'⟩
  have hs := oneHighFamilyAtomIdVal_semanticSound R h.semantic
    (.edge (min y x) (max y x))
  rw [hout] at hs
  have hr := oneHighFamilyAtomIdVal_result R
    (.edge (min y x) (max y x)) st val
  rw [hout] at hr
  dsimp at hr
  have hstate := oneHighFamilyAtomIdVal_state R
    (.edge (min y x) (max y x)) st val
  rw [hout] at hstate
  have htop : st.top ≤ acc'.1.top := by
    rw [hstate]
    exact oneHighFamilyAtomId_top_le _ st
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

theorem oneHighFamilyCollectEdgeVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y x : Nat) {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyCollectEdgeVal R y x input).2.1.ids := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyCollectEdgeVal, oneHighFamilyEdgeIdVal]
  exact oneHighFamilyAtomIdVal_old_mem R
    (.edge (min y x) (max y x)) st val hmem

theorem oneHighFamilyCollectEdgesListVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (xs : List Nat)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (xs.foldl
      (fun input x => oneHighFamilyCollectEdgeVal R y x input) input).2.1.ids := by
  induction xs generalizing input with
  | nil => exact hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyCollectEdgeVal_old_mem R y x hmem)

def oneHighFamilyInputAccumRow
    (input : Array Int × OneHighFamilyValState) :
    Fin input.1.size → Bool :=
  oneHighFamilyLiteralRow input.2.2 input.1

theorem oneHighFamilyInputAccum_reifies
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyInputAccumSound R input) :
    SeqCounterInputReifies input.2.2 input.2.1.top input.1
      (oneHighFamilyInputAccumRow input) where
  size_eq := rfl
  nonzero := by
    intro i hi
    apply h.nonzero
    rw [show input.1.getD i 0 = input.1[i] by
      simp [Array.getD, hi]]
    exact Array.getElem_mem hi
  bounded := by
    intro i hi
    apply h.bounded
    rw [show input.1.getD i 0 = input.1[i] by
      simp [Array.getD, hi]]
    exact Array.getElem_mem hi
  value := by
    intro i hi
    rfl

noncomputable def oneHighFamilyCollectFarInputsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  (oneHighFamilyFarVertices y).foldl
    (fun input x => oneHighFamilyCollectEdgeVal R y x input) (#[], acc)

theorem oneHighFamilyCollectEdgeVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y x : Nat) (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyCollectEdgeVal R y x input
    let raw :=
      let (id, st) := oneHighFamilyEdgeId y x input.2.1
      (input.1.push (id : Int), st)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  rcases input with ⟨vars, st, val⟩
  simp only [oneHighFamilyCollectEdgeVal, oneHighFamilyEdgeIdVal,
    oneHighFamilyEdgeId]
  generalize hv : oneHighFamilyAtomIdVal R
    (.edge (min y x) (max y x)) (st, val) = outVal
  rcases outVal with ⟨idVal, stVal, val'⟩
  generalize hs : oneHighFamilyAtomId
    (.edge (min y x) (max y x)) st = out
  rcases out with ⟨id, st'⟩
  have hid := oneHighFamilyAtomIdVal_id R
    (.edge (min y x) (max y x)) st val
  have hstate := oneHighFamilyAtomIdVal_state R
    (.edge (min y x) (max y x)) st val
  rw [hv, hs] at hid hstate
  exact ⟨by simp_all, by simp_all⟩

theorem oneHighFamilyCollectEdgesListVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (xs : List Nat) (input : Array Int × OneHighFamilyValState) :
    let out := xs.foldl
      (fun input x => oneHighFamilyCollectEdgeVal R y x input) input
    let raw := xs.foldl (fun input x =>
      let (id, st) := oneHighFamilyEdgeId y x input.2
      (input.1.push (id : Int), st)) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction xs generalizing input with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyCollectEdgeVal_projection R y x input
      have hi := ih (oneHighFamilyCollectEdgeVal R y x input)
      rcases hp with ⟨hvars, hst⟩
      simpa [hvars, hst] using hi

theorem oneHighFamilyCollectEdgesListVal_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (xs : List Nat)
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyInputAccumSound R input) :
    OneHighFamilyInputAccumSound R
      (xs.foldl (fun input x => oneHighFamilyCollectEdgeVal R y x input)
        input) := by
  induction xs generalizing input with
  | nil => exact h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyCollectEdgeVal_sound R h y x)

noncomputable def oneHighFamilyCollectEdgesListVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (xs : List Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedEdgesMatch y xs
      (xs.foldl (fun input x => oneHighFamilyCollectEdgeVal R y x input)
        (#[], acc)) := by
  suffices ∀ pre : List Nat,
      OneHighFamilyCollectedEdgesMatch y pre
        (pre.foldl (fun input x => oneHighFamilyCollectEdgeVal R y x input)
          (#[], acc)) by
    exact this xs
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact oneHighFamilyCollectedEdgesMatch_empty y acc
  | append_singleton pre x ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact oneHighFamilyCollectedEdgesMatch_push R ih

theorem oneHighFamilyCollectFarInputsVal_sound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc) (y : Nat) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyCollectFarInputsVal R y acc) := by
  unfold oneHighFamilyCollectFarInputsVal
  exact oneHighFamilyCollectEdgesListVal_sound R y _
    (oneHighFamilyInputAccumSound_empty R h)

noncomputable def oneHighFamilyCollectFarInputsVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (y : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedEdgesMatch y (oneHighFamilyFarVertices y)
      (oneHighFamilyCollectFarInputsVal R y acc) := by
  exact oneHighFamilyCollectEdgesListVal_match R y _ acc

theorem oneHighFamilyCollectedEdgesMatch_length
    {y : Nat} {xs : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedEdgesMatch y xs input) :
    input.1.size = xs.length := by
  have hvars := congrArg List.length h.vars_eq
  have halign := h.aligned.length_eq
  simpa using hvars.trans (by simpa using halign.symm)

theorem oneHighFamilyCollectedEdgesMatch_value
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y : Nat} (hy : y < 40) {xs : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedEdgesMatch y xs input)
    (hs : OneHighFamilySemanticSound R input.2)
    (i : Nat) (hi : i < input.1.size)
    (hx : xs.get ⟨i, by
      rw [← oneHighFamilyCollectedEdgesMatch_length h]; exact hi⟩ < 40) :
    dimacsLitValue input.2.2 (input.1.getD i 0) =
      decide (R.Adj (⟨y, hy⟩ : Fin 40)
        ⟨xs.get ⟨i, by
          rw [← oneHighFamilyCollectedEdgesMatch_length h]; exact hi⟩, hx⟩) := by
  have hidsLen : h.ids.length = xs.length := h.aligned.length_eq.symm
  have hiIds : i < h.ids.length := by
    rw [hidsLen]
    rw [← oneHighFamilyCollectedEdgesMatch_length h]
    exact hi
  have hiXs : i < xs.length := by
    rw [← oneHighFamilyCollectedEdgesMatch_length h]
    exact hi
  have halign := h.aligned.get hiXs hiIds
  have hiList : i < input.1.toList.length := by simpa using hi
  have hlistGet : input.1.toList[i] = (h.ids.get ⟨i, hiIds⟩ : Int) := by
    have hx := List.get_of_eq h.vars_eq ⟨i, hiList⟩
    rw [List.get_eq_getElem] at hx
    have hiMap : i < (List.map (fun id : Nat => Int.ofNat id) h.ids).length := by
      simpa using hiIds
    calc
      input.1.toList[i] =
          (List.map (fun id : Nat => Int.ofNat id) h.ids)[i]'hiMap := hx
      _ = (h.ids[i]'hiIds : Int) := List.getElem_map _
      _ = (h.ids.get ⟨i, hiIds⟩ : Int) := by
        rw [List.get_eq_getElem]
  have harrayGet : input.1.getD i 0 = (h.ids.get ⟨i, hiIds⟩ : Int) := by
    rw [show input.1.getD i 0 = input.1[i] by simp [Array.getD, hi]]
    rw [← Array.getElem_toList hi]
    exact hlistGet
  rw [harrayGet]
  have hidPos := (hs.ids.id_bounds _ halign).1
  have hidPosInt : 0 < (h.ids.get ⟨i, hiIds⟩ : Int) := by
    exact_mod_cast hidPos
  rw [dimacsLitValue, if_pos hidPosInt]
  simpa using (hs.named _ _ halign).trans
    (oneHighFamilyAtomValue_edge R hy hx)

theorem oneHighFamilyCollectedEdgesMatch_notBoth
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y : Nat} (hy : y < 40) {xs : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedEdgesMatch y xs input)
    (hs : OneHighFamilySemanticSound R input.2)
    {atomId : Nat}
    (hxs : ∀ z ∈ xs, z < 40)
    (hnot : input.2.2 atomId = true → ∀ z (hz : z ∈ xs),
      ∀ hzlt : z < 40,
        ¬ R.Adj (⟨y, hy⟩ : Fin 40) ⟨z, hzlt⟩) :
    ∀ id ∈ h.ids,
      ¬(input.2.2 atomId = true ∧ input.2.2 id = true) := by
  have go : ∀ {zs ids : List Nat},
      List.Forall₂ (fun z id =>
        ((.edge (min y z) (max y z)), id) ∈ input.2.1.ids) zs ids →
      (∀ z ∈ zs, z < 40) →
      (input.2.2 atomId = true → ∀ z (hz : z ∈ zs),
        ∀ hzlt : z < 40,
          ¬ R.Adj (⟨y, hy⟩ : Fin 40) ⟨z, hzlt⟩) →
      ∀ id ∈ ids,
        ¬(input.2.2 atomId = true ∧ input.2.2 id = true) := by
    intro zs ids haligned
    induction haligned with
    | nil => simp
    | @cons z id zs ids hedge haligned ih =>
        intro hzs hn id' hid'
        simp only [List.mem_cons] at hid'
        rcases hid' with rfl | hid'
        · intro hboth
          have hzmem : z ∈ z :: zs := by simp
          have hzlt := hzs z hzmem
          have hedgeVal := (hs.named _ id' hedge).trans
            (oneHighFamilyAtomValue_edge R hy hzlt)
          rw [hedgeVal] at hboth
          simp only [decide_eq_true_eq] at hboth
          exact hn hboth.1 z hzmem hzlt hboth.2
        · apply ih
          · intro z' hz'
            exact hzs z' (by simp [hz'])
          · intro hmiss z' hz' hzlt hadj
            exact hn hmiss z' (by simp [hz']) hzlt hadj
          · exact hid'
  exact go h.aligned hxs hnot

theorem oneHighFamilyCollectedBlock_positive
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {w b : Nat} (hw : w < 40) (hb : b < 8)
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedEdgesMatch w
      (oneHighFamilyBlockVertices b) input)
    (hs : OneHighFamilySemanticSound R input.2)
    {xv : Nat} (hxv : ((.miss w b), xv) ∈ input.2.1.ids) :
    input.2.2 xv = true ∨ ∃ id ∈ h.ids, input.2.2 id = true := by
  cases hv : input.2.2 xv with
  | true => exact Or.inl rfl
  | false =>
      right
      have hmissVal := hs.named (.miss w b) xv hxv
      simp [oneHighFamilyAtomValue, hw, hb] at hmissVal
      have hnmiss : ¬ oneHighFamilyMissesBlock R
          (⟨w, hw⟩ : Fin 40) (⟨b, hb⟩ : Fin 8) := by
        intro hmiss
        have : input.2.2 xv = true := by
          rw [hmissVal]
          simp [hmiss]
        rw [hv] at this
        contradiction
      rw [oneHighFamilyMissesBlock_iff_blockVertices R hw hb] at hnmiss
      push_neg at hnmiss
      rcases hnmiss with ⟨z, hz, hadj⟩
      rcases listForall₂_exists_right_of_mem h.aligned hz with
        ⟨id, hid, hedge⟩
      refine ⟨id, hid, ?_⟩
      have hzlt := (oneHighFamilyBlockVertices_mem hb hz).1
      rw [(hs.named _ id hedge).trans
        (oneHighFamilyAtomValue_edge R hw hzlt)]
      simp only [decide_eq_true_eq]
      exact hadj

def oneHighFamilyEmitMissPairsVal (xv : Nat) (ids : List Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  List.foldl (fun (acc : OneHighFamilyValState) (id : Nat) =>
    (oneHighFamilyEmitVal [-(xv : Int), -(id : Int)] acc).2) acc ids

@[simp] theorem oneHighFamilyEmitMissPairsVal_ids
    (xv : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitMissPairsVal xv ids acc).1.ids = acc.1.ids := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitMissPairsVal xv ids
        (oneHighFamilyEmitVal [-(xv : Int), -(id : Int)] acc).2).1.ids = _
      rw [ih]
      rfl

@[simp] theorem oneHighFamilyEmitMissPairsVal_value
    (xv : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitMissPairsVal xv ids acc).2 = acc.2 := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitMissPairsVal xv ids
        (oneHighFamilyEmitVal [-(xv : Int), -(id : Int)] acc).2).2 = _
      rw [ih]
      rfl

theorem oneHighFamilyEmitMissPairsVal_state
    (xv : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitMissPairsVal xv ids acc).1 =
      List.foldl (fun (st : OneHighFamilyGenState) (id : Nat) =>
        (oneHighFamilyEmit [-(xv : Int), -(id : Int)] st).2) acc.1 ids := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitMissPairsVal xv ids
        (oneHighFamilyEmitVal [-(xv : Int), -(id : Int)] acc).2).1 = _
      rw [ih]
      rfl

theorem oneHighFamilyEmitMissPairsVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {xv : Nat} {ids : List Nat} {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hxv : ∃ atom, (atom, xv) ∈ acc.1.ids)
    (hids : ∀ id ∈ ids, ∃ atom, (atom, id) ∈ acc.1.ids)
    (hnot : ∀ id ∈ ids,
      ¬(acc.2 xv = true ∧ acc.2 id = true)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyEmitMissPairsVal xv ids acc) := by
  induction ids generalizing acc with
  | nil => exact h
  | cons id ids ih =>
      simp only [oneHighFamilyEmitMissPairsVal, List.foldl_cons]
      let next := (oneHighFamilyEmitVal
        [-(xv : Int), -(id : Int)] acc).2
      have hidMem := hids id (by simp)
      have hstep : OneHighFamilySemanticSound R next := by
        apply oneHighFamilyEmitVal_semanticSound R h
        · exact dimacsClauseSatisfied_negative_pair (hnot id (by simp))
        · exact dimacsClauseBounded_negative_pair
            (h.ids.id_bounds _ hxv.choose_spec).2
            (h.ids.id_bounds _ hidMem.choose_spec).2
      have hidsEq : next.1.ids = acc.1.ids := by
        rfl
      apply ih hstep
      · rcases hxv with ⟨atom, hatom⟩
        exact ⟨atom, by rw [hidsEq]; exact hatom⟩
      · intro id' hid'
        rcases hids id' (by simp [hid']) with ⟨atom, hatom⟩
        exact ⟨atom, by rw [hidsEq]; exact hatom⟩
      · intro id' hid'
        simpa [next, oneHighFamilyEmitVal] using hnot id' (by simp [hid'])

theorem oneHighFamilyFarVertices_nodup (y : Nat) :
    (oneHighFamilyFarVertices y).Nodup := by
  exact (List.nodup_range : (List.range 40).Nodup).filter _

theorem mem_oneHighEncodedFarNeighbors_iff_farVertices
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y x : Nat} (hy : y < 40) (hx : x < 40) :
    (⟨x, hx⟩ : Fin 40) ∈
        oneHighEncodedFarNeighbors R (⟨y, hy⟩ : Fin 40) ↔
      x ∈ oneHighFamilyFarVertices y ∧
        R.Adj (⟨y, hy⟩ : Fin 40) (⟨x, hx⟩ : Fin 40) := by
  rw [oneHighFamilyFarVertices_mem_iff hy]
  simp only [oneHighEncodedFarNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.divNat]
  constructor
  · rintro ⟨ha, hblock, hmate⟩
    refine ⟨⟨hx, ?_, ?_, ?_⟩, ha⟩
    · intro hxy
      subst x
      exact hblock rfl
    · intro heq
      apply hblock
      exact Fin.ext heq
    · intro heq
      apply hmate
      exact Fin.ext heq
  · rintro ⟨⟨_, _, hblock, hmate⟩, ha⟩
    refine ⟨ha, ?_, ?_⟩
    · intro heq
      apply hblock
      exact congrArg Fin.val heq
    intro heq
    apply hmate
    exact congrArg Fin.val heq

theorem oneHighFamilyCollectedFar_trueCard
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y : Nat} (hy : y < 40) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    let input := oneHighFamilyCollectFarInputsVal R y acc
    Fintype.card {i : Fin input.1.size //
      oneHighFamilyInputAccumRow input i = true} =
    Fintype.card {z : {x // x ∈ oneHighFamilyFarVertices y} //
      R.Adj (⟨y, hy⟩ : Fin 40) ⟨z.1, by
        exact (oneHighFamilyFarVertices_mem_iff hy).mp z.2 |>.1⟩} := by
  let input := oneHighFamilyCollectFarInputsVal R y acc
  let xs := oneHighFamilyFarVertices y
  let hm := oneHighFamilyCollectFarInputsVal_match R y acc
  let hs := oneHighFamilyCollectFarInputsVal_sound R hacc y
  have hlen : input.1.size = xs.length :=
    oneHighFamilyCollectedEdgesMatch_length hm
  let e : Fin input.1.size ≃ {x // x ∈ xs} :=
    (finCongr hlen).trans ((oneHighFamilyFarVertices_nodup y).getEquiv xs)
  let ep : {i : Fin input.1.size //
      oneHighFamilyInputAccumRow input i = true} ≃
      {z : {x // x ∈ xs} //
        R.Adj (⟨y, hy⟩ : Fin 40) ⟨z.1, by
          exact (oneHighFamilyFarVertices_mem_iff hy).mp z.2 |>.1⟩} :=
    Equiv.subtypeEquiv e (by
      intro i
      have hgetMem : xs.get (finCongr hlen i) ∈ xs :=
        List.get_mem xs (finCongr hlen i)
      have hx : xs.get (finCongr hlen i) < 40 :=
        (oneHighFamilyFarVertices_mem_iff hy).mp hgetMem |>.1
      have hv := oneHighFamilyCollectedEdgesMatch_value R hy hm hs.semantic
        i.val i.isLt hx
      have hv' : oneHighFamilyInputAccumRow input i =
          decide (R.Adj (⟨y, hy⟩ : Fin 40)
            ⟨xs.get (finCongr hlen i), hx⟩) := by
        unfold oneHighFamilyInputAccumRow oneHighFamilyLiteralRow
        convert hv using 1 <;> simp [input, xs, finCongr]
      rw [hv']
      simp [e, xs])
  exact Fintype.card_congr ep

theorem oneHighFamilyFarNeighborSubtype_card
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {y : Nat} (hy : y < 40) :
    Fintype.card {z : {x // x ∈ oneHighFamilyFarVertices y} //
      R.Adj (⟨y, hy⟩ : Fin 40) ⟨z.1, by
        exact (oneHighFamilyFarVertices_mem_iff hy).mp z.2 |>.1⟩} =
      (oneHighEncodedFarNeighbors R (⟨y, hy⟩ : Fin 40)).card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun z =>
      let hx := (oneHighFamilyFarVertices_mem_iff hy).mp z.1.2 |>.1
      ⟨⟨z.1.1, hx⟩,
        (mem_oneHighEncodedFarNeighbors_iff_farVertices R hy hx).mpr
          ⟨z.1.2, z.2⟩⟩
    invFun := fun z =>
      let hz := (mem_oneHighEncodedFarNeighbors_iff_farVertices R hy z.1.2).mp z.2
      ⟨⟨z.1.1, hz.1⟩, hz.2⟩
    left_inv := by intro z; ext; rfl
    right_inv := by intro z; ext; rfl }

theorem oneHighFamilyCollectFarInputsVal_count
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {y : Nat} (hy : y < 40) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    let input := oneHighFamilyCollectFarInputsVal R y acc
    seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
      oneHighFamilyFarDegreeBound a y := by
  let input := oneHighFamilyCollectFarInputsVal R y acc
  have hfar := hc.relation.2.2.2.2.2.1 (⟨y, hy⟩ : Fin 40)
  calc
    seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
        ((Finset.range input.1.size).filter fun i =>
          dimacsLitValue input.2.2 (input.1.getD i 0)).card := by
            exact seqPrefixTrue_oneHighFamilyLiteralRow input.2.2 input.1
    _ = Fintype.card {i : Fin input.1.size //
          oneHighFamilyInputAccumRow input i = true} := by
            rw [← finsetRangeFilter_card_eq_finSubtype_card input.1.size
              (fun i => oneHighFamilyInputAccumRow input i = true)]
            congr 1
            ext i
            simp [oneHighFamilyInputAccumRow, oneHighFamilyLiteralRow]
    _ = Fintype.card {z : {x // x ∈ oneHighFamilyFarVertices y} //
          R.Adj (⟨y, hy⟩ : Fin 40) ⟨z.1, by
            exact (oneHighFamilyFarVertices_mem_iff hy).mp z.2 |>.1⟩} :=
          oneHighFamilyCollectedFar_trueCard R hy hacc
    _ = (oneHighEncodedFarNeighbors R (⟨y, hy⟩ : Fin 40)).card :=
          oneHighFamilyFarNeighborSubtype_card R hy
    _ = oneHighFamilyFarDegreeBound a y := by
          rw [hfar]
          exact (oneHighFamilyFarDegreeBound_eq a y hy).symm

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

noncomputable def oneHighFamilyFarDegreeStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a y : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let input := oneHighFamilyCollectFarInputsVal R y acc
  oneHighFamilyEqualsBlockVal input.1 (oneHighFamilyInputAccumRow input)
    (oneHighFamilyFarDegreeBound a y) input.2

theorem oneHighFamilyFarDegreeStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {y : Nat} (hy : y < 40) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyFarDegreeStepVal R a y acc) := by
  let input := oneHighFamilyCollectFarInputsVal R y acc
  apply oneHighFamilyEqualsBlockVal_semanticSound R
    (oneHighFamilyCollectFarInputsVal_sound R hacc y).semantic
  · exact oneHighFamilyInputAccum_reifies R
      (oneHighFamilyCollectFarInputsVal_sound R hacc y)
  · exact oneHighFamilyCollectFarInputsVal_count a R hc hy hacc

theorem oneHighFamilyFarDegreeStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a y : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyFarDegreeStepVal R a y acc).1 =
      oneHighFamilyFarDegreeStep a y acc.1 := by
  have hp := oneHighFamilyCollectEdgesListVal_projection R y
    (oneHighFamilyFarVertices y) (#[], acc)
  unfold oneHighFamilyFarDegreeStepVal oneHighFamilyCollectFarInputsVal
  unfold oneHighFamilyFarDegreeStep
  generalize hv : (oneHighFamilyFarVertices y).foldl
    (fun input x => oneHighFamilyCollectEdgeVal R y x input) (#[], acc) = input
  rcases input with ⟨vars, st, val⟩
  rw [hv] at hp
  generalize hs : (oneHighFamilyFarVertices y).foldl (fun input x =>
    let (id, st) := oneHighFamilyEdgeId y x input.2
    (input.1.push (id : Int), st)) (#[], acc.1) = raw
  rcases raw with ⟨rawVars, rawSt⟩
  rw [hs] at hp
  rcases hp with ⟨rfl, rfl⟩
  simp

noncomputable def oneHighFamilyFarDegreeClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40)
    (oneHighFamilyFarDegreeStepVal R a)
    (oneHighFamilyAtMostOneBlockClausesVal R a val)

theorem oneHighFamilyFarDegreeClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyFarDegreeClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyAtMostOneBlockClausesVal_semanticSound a R hc val)
  intro y hy acc hacc
  exact oneHighFamilyFarDegreeStepVal_semanticSound a R hc
    (List.mem_range.mp hy) hacc

theorem oneHighFamilyFarDegreeClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyFarDegreeClausesVal R a val).1 =
      oneHighFamilyFarDegreeClauses a := by
  unfold oneHighFamilyFarDegreeClausesVal oneHighFamilyFarDegreeClauses
  calc
    _ = oneHighFamilyRunList (List.range 40)
        (oneHighFamilyFarDegreeStep a)
        (oneHighFamilyAtMostOneBlockClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun y acc => oneHighFamilyFarDegreeStepVal_state R a y acc)
    _ = _ := by rw [oneHighFamilyAtMostOneBlockClausesVal_state]

noncomputable def oneHighFamilyMissDefinitionStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (w b : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  if b = w / 5 ∨ b = (w / 5 ^^^ 1) then acc else
    let (xv, acc) := oneHighFamilyAtomIdVal R (.miss w b) acc
    let input := (oneHighFamilyBlockVertices b).foldl
      (fun input z => oneHighFamilyCollectEdgeVal R w z input) (#[], acc)
    let hm := oneHighFamilyCollectEdgesListVal_match R w
      (oneHighFamilyBlockVertices b) acc
    let acc := oneHighFamilyEmitMissPairsVal xv hm.ids input.2
    (oneHighFamilyEmitVal
      ((xv : Int) :: List.map (fun id : Nat => (id : Int)) hm.ids) acc).2

theorem oneHighFamilyMissDefinitionStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {w b : Nat} (hw : w < 40) (hb : b < 8)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMissDefinitionStepVal R w b acc) := by
  simp only [oneHighFamilyMissDefinitionStepVal]
  split
  · exact hacc
  · generalize ha : oneHighFamilyAtomIdVal R (.miss w b) acc = out
    rcases out with ⟨xv, acc₁⟩
    have hs₁ := oneHighFamilyAtomIdVal_semanticSound R hacc (.miss w b)
    rw [ha] at hs₁
    have hr₁ := oneHighFamilyAtomIdVal_result R (.miss w b) acc.1 acc.2
    rw [ha] at hr₁
    let input := (oneHighFamilyBlockVertices b).foldl
      (fun input z => oneHighFamilyCollectEdgeVal R w z input) (#[], acc₁)
    let hm := oneHighFamilyCollectEdgesListVal_match R w
      (oneHighFamilyBlockVertices b) acc₁
    have hsInput : OneHighFamilySemanticSound R input.2 :=
      (oneHighFamilyCollectEdgesListVal_sound R w _
        (oneHighFamilyInputAccumSound_empty R hs₁)).semantic
    have hxvInput : ((.miss w b), xv) ∈ input.2.1.ids := by
      exact oneHighFamilyCollectEdgesListVal_old_mem R w _ hr₁.1
    have hbounds : ∀ z ∈ oneHighFamilyBlockVertices b, z < 40 := by
      intro z hz
      exact (oneHighFamilyBlockVertices_mem hb hz).1
    have hmissImp : input.2.2 xv = true →
        ∀ z (hz : z ∈ oneHighFamilyBlockVertices b) (hzlt : z < 40),
          ¬ R.Adj (⟨w, hw⟩ : Fin 40) ⟨z, hzlt⟩ := by
      intro hxv z hz hzlt
      have hmissVal := hsInput.named (.miss w b) xv hxvInput
      simp [oneHighFamilyAtomValue, hw, hb] at hmissVal
      have hmiss : oneHighFamilyMissesBlock R
          (⟨w, hw⟩ : Fin 40) (⟨b, hb⟩ : Fin 8) := by
        rw [hmissVal] at hxv
        simpa using hxv
      have hn := (oneHighFamilyMissesBlock_iff_blockVertices R hw hb).mp
        hmiss z hz
      simpa using hn
    have hnot := oneHighFamilyCollectedEdgesMatch_notBoth R hw hm hsInput
      hbounds hmissImp
    have hids : ∀ id ∈ hm.ids,
        ∃ atom, (atom, id) ∈ input.2.1.ids := by
      intro id hid
      rcases listForall₂_exists_left_of_mem hm.aligned hid with
        ⟨z, _, hedge⟩
      exact ⟨.edge (min w z) (max w z), hedge⟩
    let pairs := oneHighFamilyEmitMissPairsVal xv hm.ids input.2
    have hsPairs : OneHighFamilySemanticSound R pairs :=
      oneHighFamilyEmitMissPairsVal_semanticSound R hsInput
        ⟨.miss w b, hxvInput⟩ hids hnot
    apply oneHighFamilyEmitVal_semanticSound R hsPairs
    · apply dimacsClauseSatisfied_positive_ids
      · exact (hsPairs.ids.id_bounds _ (by
          simpa [pairs] using hxvInput)).1
      · intro id hid
        exact (hsPairs.ids.id_bounds _ (by
          simpa [pairs] using (hids id hid).choose_spec)).1
      · have hp := oneHighFamilyCollectedBlock_positive R hw hb hm
          hsInput hxvInput
        change pairs.2 xv = true ∨ ∃ id ∈ hm.ids, pairs.2 id = true
        rw [oneHighFamilyEmitMissPairsVal_value]
        exact hp
    · apply dimacsClauseBounded_positive_ids
      · exact (hsPairs.ids.id_bounds _ (by
          simpa [pairs] using hxvInput)).2
      · intro id hid
        exact (hsPairs.ids.id_bounds _ (by
          simpa [pairs] using (hids id hid).choose_spec)).2

theorem oneHighFamilyMissDefinitionStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (w b : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyMissDefinitionStepVal R w b acc).1 =
      oneHighFamilyMissDefinitionStep w b acc.1 := by
  unfold oneHighFamilyMissDefinitionStepVal oneHighFamilyMissDefinitionStep
  split
  · rfl
  · generalize hv : oneHighFamilyAtomIdVal R (.miss w b) acc = outVal
    rcases outVal with ⟨xv, acc₁⟩
    generalize hg : oneHighFamilyAtomId (.miss w b) acc.1 = out
    rcases out with ⟨xg, st₁⟩
    have hid := oneHighFamilyAtomIdVal_id R (.miss w b) acc.1 acc.2
    have hstate := oneHighFamilyAtomIdVal_state R (.miss w b) acc.1 acc.2
    rw [hv, hg] at hid hstate
    dsimp at hid hstate
    subst xg
    let input := (oneHighFamilyBlockVertices b).foldl
      (fun input z => oneHighFamilyCollectEdgeVal R w z input) (#[], acc₁)
    let raw := (oneHighFamilyBlockVertices b).foldl (fun input z =>
      let (id, st) := oneHighFamilyEdgeId w z input.2
      (input.1.push (id : Int), st)) (#[], st₁)
    generalize hraw : raw = rawOut
    rcases rawOut with ⟨rawVars, rawSt⟩
    have hp := oneHighFamilyCollectEdgesListVal_projection R w
      (oneHighFamilyBlockVertices b) (#[], acc₁)
    rw [hstate] at hp
    change input.1 = raw.1 ∧ input.2.1 = raw.2 at hp
    rw [hraw] at hp
    let hm := oneHighFamilyCollectEdgesListVal_match R w
      (oneHighFamilyBlockVertices b) acc₁
    have hvars : input.1.toList =
        List.map (fun id : Nat => (id : Int)) hm.ids := hm.vars_eq
    rw [oneHighFamilyEmitVal_state]
    rw [oneHighFamilyEmitMissPairsVal_state]
    rcases hp with ⟨hinput, hst⟩
    have hrawVars : rawVars.toList =
        List.map (fun id : Nat => (id : Int)) hm.ids := by
      exact (congrArg Array.toList hinput).symm.trans hvars
    rw [hst]
    change _ = (let (lits, st) := raw
      let st := lits.foldl
        (fun st lit => (oneHighFamilyEmit [-(xv : Int), -lit] st).2) st
      (oneHighFamilyEmit ((xv : Int) :: lits.toList) st).2)
    rw [hraw]
    dsimp only
    rw [← Array.foldl_toList]
    rw [hrawVars]
    change (oneHighFamilyEmit
        ((xv : Int) :: List.map (fun id : Nat => (id : Int)) hm.ids)
        (List.foldl (fun st (id : Nat) =>
          (oneHighFamilyEmit [-(xv : Int), -(id : Int)] st).2)
          rawSt hm.ids)).2 = _
    rw [List.foldl_map]

noncomputable def oneHighFamilyMissVertexStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a w : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  if oneHighFamilyVertexMatched a w then
    oneHighFamilyRunListVal (List.range 8)
      (oneHighFamilyMissDefinitionStepVal R w) acc
  else acc

theorem oneHighFamilyMissVertexStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) {w : Nat} (hw : w < 40)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMissVertexStepVal R a w acc) := by
  simp only [oneHighFamilyMissVertexStepVal]
  split
  · apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hacc
    intro b hb acc' hs
    exact oneHighFamilyMissDefinitionStepVal_semanticSound R hw
      (List.mem_range.mp hb) hs
  · exact hacc

theorem oneHighFamilyMissVertexStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a w : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyMissVertexStepVal R a w acc).1 =
      oneHighFamilyMissVertexStep a w acc.1 := by
  unfold oneHighFamilyMissVertexStepVal oneHighFamilyMissVertexStep
  split
  · exact oneHighFamilyRunListVal_state _ _ _ _
      (fun b acc' => oneHighFamilyMissDefinitionStepVal_state R w b acc')
  · rfl

noncomputable def oneHighFamilyMissDefinitionClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 40)
    (oneHighFamilyMissVertexStepVal R a)
    (oneHighFamilyFarDegreeClausesVal R a val)

theorem oneHighFamilyMissDefinitionClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMissDefinitionClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyFarDegreeClausesVal_semanticSound a R hc val)
  intro w hw acc hacc
  exact oneHighFamilyMissVertexStepVal_semanticSound R a
    (List.mem_range.mp hw) hacc

theorem oneHighFamilyMissDefinitionClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyMissDefinitionClausesVal R a val).1 =
      oneHighFamilyMissDefinitionClauses a := by
  unfold oneHighFamilyMissDefinitionClausesVal
    oneHighFamilyMissDefinitionClauses
  calc
    _ = oneHighFamilyRunList (List.range 40)
        (oneHighFamilyMissVertexStep a)
        (oneHighFamilyFarDegreeClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun w acc => oneHighFamilyMissVertexStepVal_state R a w acc)
    _ = _ := by rw [oneHighFamilyFarDegreeClausesVal_state]

noncomputable def oneHighFamilyTwoNegativeAtomsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom₁ atom₂ : OneHighFamilyAtom)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let (id₁, acc) := oneHighFamilyAtomIdVal R atom₁ acc
  let (id₂, acc) := oneHighFamilyAtomIdVal R atom₂ acc
  (oneHighFamilyEmitVal [-(id₁ : Int), -(id₂ : Int)] acc).2

theorem oneHighFamilyTwoNegativeAtomsVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (atom₁ atom₂ : OneHighFamilyAtom)
    (acc : OneHighFamilyValState) :
    (oneHighFamilyTwoNegativeAtomsVal R atom₁ atom₂ acc).1 =
      let (id₁, st) := oneHighFamilyAtomId atom₁ acc.1
      let (id₂, st) := oneHighFamilyAtomId atom₂ st
      (oneHighFamilyEmit [-(id₁ : Int), -(id₂ : Int)] st).2 := by
  generalize h₁ : oneHighFamilyAtomId atom₁ acc.1 = out₁
  rcases out₁ with ⟨id₁, st₁⟩
  generalize h₂ : oneHighFamilyAtomId atom₂ st₁ = out₂
  rcases out₂ with ⟨id₂, st₂⟩
  simp [oneHighFamilyTwoNegativeAtomsVal, oneHighFamilyAtomIdVal,
    oneHighFamilyEmitVal, h₁, h₂]

theorem oneHighFamilyTwoNegativeAtomsVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (atom₁ atom₂ : OneHighFamilyAtom)
    (hnot : ¬(oneHighFamilyAtomValue R atom₁ = true ∧
      oneHighFamilyAtomValue R atom₂ = true)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyTwoNegativeAtomsVal R atom₁ atom₂ acc) := by
  simp only [oneHighFamilyTwoNegativeAtomsVal]
  generalize h₁ : oneHighFamilyAtomIdVal R atom₁ acc = out₁
  rcases out₁ with ⟨id₁, acc₁⟩
  have hs₁ := oneHighFamilyAtomIdVal_semanticSound R h atom₁
  rw [h₁] at hs₁
  have hr₁ := oneHighFamilyAtomIdVal_result R atom₁ acc.1 acc.2
  rw [h₁] at hr₁
  dsimp at hr₁
  generalize h₂ : oneHighFamilyAtomIdVal R atom₂ acc₁ = out₂
  rcases out₂ with ⟨id₂, acc₂⟩
  have hs₂ := oneHighFamilyAtomIdVal_semanticSound R hs₁ atom₂
  rw [h₂] at hs₂
  have hr₂ := oneHighFamilyAtomIdVal_result R atom₂ acc₁.1 acc₁.2
  rw [h₂] at hr₂
  dsimp at hr₂
  have hm₁ : (atom₁, id₁) ∈ acc₂.1.ids := by
    have hm := oneHighFamilyAtomIdVal_old_mem R atom₂
      acc₁.1 acc₁.2 hr₁.1
    rw [h₂] at hm
    exact hm
  simp only [h₂]
  apply oneHighFamilyEmitVal_semanticSound R hs₂
  · apply dimacsClauseSatisfied_negative_pair
    rw [hs₂.named atom₁ id₁ hm₁, hr₂.2]
    exact hnot
  · exact dimacsClauseBounded_negative_pair
      (hs₂.ids.id_bounds _ hm₁).2
      (hs₂.ids.id_bounds _ hr₂.1).2

noncomputable def oneHighFamilyLexPairStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x y j k : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  if j > k then
    oneHighFamilyTwoNegativeAtomsVal R (.miss x j) (.miss y k) acc
  else acc

theorem oneHighFamilyLexPairStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x y j k : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyLexPairStepVal R x y j k acc).1 =
      oneHighFamilyLexPairStep x y j k acc.1 := by
  unfold oneHighFamilyLexPairStepVal oneHighFamilyLexPairStep
  split
  · exact oneHighFamilyTwoNegativeAtomsVal_state R _ _ acc
  · rfl

theorem oneHighFamilyLexPairStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x y j k : Nat} (hx : x < 40) (hy : y < 40)
    (hj : j < 8) (hk : k < 8)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc)
    (hnot : j > k →
      ¬(oneHighFamilyMissesBlock R (⟨x, hx⟩ : Fin 40) ⟨j, hj⟩ ∧
        oneHighFamilyMissesBlock R (⟨y, hy⟩ : Fin 40) ⟨k, hk⟩)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyLexPairStepVal R x y j k acc) := by
  classical
  unfold oneHighFamilyLexPairStepVal
  split
  next hgt =>
    apply oneHighFamilyTwoNegativeAtomsVal_semanticSound R hacc
    intro hboth
    have h₁ : oneHighFamilyMissesBlock R
        (⟨x, hx⟩ : Fin 40) ⟨j, hj⟩ := by
      have hd : @decide (oneHighFamilyMissesBlock R
          (⟨x, hx⟩ : Fin 40) ⟨j, hj⟩) (Classical.propDecidable _) = true := by
        simpa [oneHighFamilyAtomValue, hx, hj] using hboth.1
      exact of_decide_eq_true hd
    have h₂ : oneHighFamilyMissesBlock R
        (⟨y, hy⟩ : Fin 40) ⟨k, hk⟩ := by
      have hd : @decide (oneHighFamilyMissesBlock R
          (⟨y, hy⟩ : Fin 40) ⟨k, hk⟩) (Classical.propDecidable _) = true := by
        simpa [oneHighFamilyAtomValue, hy, hk] using hboth.2
      exact of_decide_eq_true hd
    exact hnot hgt ⟨h₁, h₂⟩
  next => exact hacc

theorem oneHighFamilyFarBlocks_mem
    {c b : Nat} (hc : c < 8) (hb : b ∈ oneHighFamilyFarBlocks c) :
    b < 8 ∧ b ≠ c ∧
      b ≠ (oneHighStandardMate (⟨c, hc⟩ : Fin 8)).val := by
  have hfilter := List.mem_filter.mp hb
  have hb8 := List.mem_range.mp hfilter.1
  have hp : b ≠ c ∧ b ≠ (c ^^^ 1) := of_decide_eq_true hfilter.2
  rcases hp with ⟨hbc, hbmate⟩
  refine ⟨hb8, hbc, ?_⟩
  rw [oneHighStandardMate_val_eq_xor]
  exact hbmate

noncomputable def oneHighFamilyLexLeqVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (c x y : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let fars := oneHighFamilyFarBlocks c
  oneHighFamilyRunListVal fars (fun j acc =>
    oneHighFamilyRunListVal fars
      (fun k acc => oneHighFamilyLexPairStepVal R x y j k acc) acc) acc

theorem oneHighFamilyLexLeqVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {c x y : Nat} (hc : c < 8) (hx : x < 40) (hy : y < 40)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc)
    (hlex : ∀ j (hj : j ∈ oneHighFamilyFarBlocks c)
      k (hk : k ∈ oneHighFamilyFarBlocks c), j > k →
      ¬(oneHighFamilyMissesBlock R (⟨x, hx⟩ : Fin 40)
          ⟨j, (oneHighFamilyFarBlocks_mem hc hj).1⟩ ∧
        oneHighFamilyMissesBlock R (⟨y, hy⟩ : Fin 40)
          ⟨k, (oneHighFamilyFarBlocks_mem hc hk).1⟩)) :
    OneHighFamilySemanticSound R
      (oneHighFamilyLexLeqVal R c x y acc) := by
  unfold oneHighFamilyLexLeqVal
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hacc
  intro j hj acc₁ hs₁
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _ hs₁
  intro k hk acc₂ hs₂
  apply oneHighFamilyLexPairStepVal_semanticSound R hx hy
    (oneHighFamilyFarBlocks_mem hc hj).1
    (oneHighFamilyFarBlocks_mem hc hk).1 hs₂
  exact hlex j hj k hk

theorem oneHighFamilyLexLeqVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (c x y : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyLexLeqVal R c x y acc).1 =
      oneHighFamilyLexLeq c x y acc.1 := by
  unfold oneHighFamilyLexLeqVal oneHighFamilyLexLeq
  apply oneHighFamilyRunListVal_state
  intro j acc'
  exact oneHighFamilyRunListVal_state _ _ _ _
    (fun k acc'' => oneHighFamilyLexPairStepVal_state R x y j k acc'')

noncomputable def oneHighFamilyLexBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a c : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let base := 5 * c
  let acc := oneHighFamilyLexLeqVal R c base (base + 1) acc
  if ¬(c % 2 = 0 ∧ c / 2 < a) then
    let acc := oneHighFamilyLexLeqVal R c (base + 2) (base + 3) acc
    oneHighFamilyLexLeqVal R c base (base + 2) acc
  else acc

theorem oneHighFamilyLexBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {c : Nat} (hc8 : c < 8) {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyLexBlockStepVal R a c acc) := by
  let cf : Fin 8 := ⟨c, hc8⟩
  have hcoord (r : Fin 5) :
      (⟨5 * c + r.val, by omega⟩ : Fin 40) =
        oneHighFamilyVertex cf r := by
    apply Fin.ext
    symm
    exact oneHighFamilyVertex_val cf r
  have hlexAt (r s : Fin 5)
      (hcase : (r = 0 ∧ s = 1) ∨
        ((r = 2 ∧ s = 3) ∨ (r = 0 ∧ s = 2)) ∧
          oneHighFamilyInternalEdges a cf = 2) : ∀ j
      (hj : j ∈ oneHighFamilyFarBlocks c) k
      (hk : k ∈ oneHighFamilyFarBlocks c), j > k →
      ¬(oneHighFamilyMissesBlock R
          (⟨5 * c + r.val, by omega⟩ : Fin 40)
            ⟨j, (oneHighFamilyFarBlocks_mem hc8 hj).1⟩ ∧
        oneHighFamilyMissesBlock R
          (⟨5 * c + s.val, by omega⟩ : Fin 40)
            ⟨k, (oneHighFamilyFarBlocks_mem hc8 hk).1⟩) := by
    intro j hj k hk hjk
    let jf : Fin 8 := ⟨j, (oneHighFamilyFarBlocks_mem hc8 hj).1⟩
    let kf : Fin 8 := ⟨k, (oneHighFamilyFarBlocks_mem hc8 hk).1⟩
    have hjc : jf ≠ cf := Fin.ne_of_val_ne
      (oneHighFamilyFarBlocks_mem hc8 hj).2.1
    have hjm : jf ≠ oneHighStandardMate cf := Fin.ne_of_val_ne
      (oneHighFamilyFarBlocks_mem hc8 hj).2.2
    have hkc : kf ≠ cf := Fin.ne_of_val_ne
      (oneHighFamilyFarBlocks_mem hc8 hk).2.1
    have hkm : kf ≠ oneHighStandardMate cf := Fin.ne_of_val_ne
      (oneHighFamilyFarBlocks_mem hc8 hk).2.2
    have hall := hc.lex cf jf kf hjc hjm hkc hkm hjk
    rw [hcoord r, hcoord s]
    rcases hcase with ⟨⟨rfl, rfl⟩⟩ | ⟨hcase, hinternal⟩
    · exact hall.1
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hall.2 hinternal).1
      · exact (hall.2 hinternal).2
  unfold oneHighFamilyLexBlockStepVal
  have hsBase := oneHighFamilyLexLeqVal_semanticSound R hc8
    (by omega : 5 * c < 40) (by omega : 5 * c + 1 < 40) hacc
    (hlexAt 0 1 (Or.inl ⟨rfl, rfl⟩))
  split
  next htwo =>
    have hinternal : oneHighFamilyInternalEdges a cf = 2 := by
      simp [oneHighFamilyInternalEdges, cf, htwo]
    have hs23 := oneHighFamilyLexLeqVal_semanticSound R hc8
      (by omega : 5 * c + 2 < 40) (by omega : 5 * c + 3 < 40)
      hsBase (hlexAt 2 3 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hinternal⟩))
    exact oneHighFamilyLexLeqVal_semanticSound R hc8
      (by omega : 5 * c < 40) (by omega : 5 * c + 2 < 40)
      hs23 (hlexAt 0 2 (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hinternal⟩))
  next => exact hsBase

theorem oneHighFamilyLexBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a c : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyLexBlockStepVal R a c acc).1 =
      oneHighFamilyLexBlockStep a c acc.1 := by
  simp only [oneHighFamilyLexBlockStepVal, oneHighFamilyLexBlockStep]
  split
  · rw [oneHighFamilyLexLeqVal_state, oneHighFamilyLexLeqVal_state,
      oneHighFamilyLexLeqVal_state]
  · rw [oneHighFamilyLexLeqVal_state]

noncomputable def oneHighFamilyLexClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 8)
    (oneHighFamilyLexBlockStepVal R a)
    (oneHighFamilyMissDefinitionClausesVal R a val)

theorem oneHighFamilyLexClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R
      (oneHighFamilyLexClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyMissDefinitionClausesVal_semanticSound a R hc val)
  intro c hc8 acc hacc
  exact oneHighFamilyLexBlockStepVal_semanticSound a R hc
    (List.mem_range.mp hc8) hacc

theorem oneHighFamilyLexClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyLexClausesVal R a val).1 =
      oneHighFamilyLexClauses a := by
  unfold oneHighFamilyLexClausesVal oneHighFamilyLexClauses
  calc
    _ = oneHighFamilyRunList (List.range 8)
        (oneHighFamilyLexBlockStep a)
        (oneHighFamilyMissDefinitionClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun c acc => oneHighFamilyLexBlockStepVal_state R a c acc)
    _ = _ := by rw [oneHighFamilyMissDefinitionClausesVal_state]

noncomputable def oneHighFamilyMidpointTseitinStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z w : Nat) (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (ts, acc) := input
  let (t, acc) := oneHighFamilyAtomIdVal R
    (.midpoint (min x z) w (max x z)) acc
  let (exw, acc) := oneHighFamilyEdgeIdVal R x w acc
  let (ewz, acc) := oneHighFamilyEdgeIdVal R w z acc
  let acc := (oneHighFamilyEmitVal [-(t : Int), (exw : Int)] acc).2
  let acc := (oneHighFamilyEmitVal [-(t : Int), (ewz : Int)] acc).2
  let acc := (oneHighFamilyEmitVal
    [(t : Int), -(exw : Int), -(ewz : Int)] acc).2
  (ts.push (t : Int), acc)

theorem oneHighFamilyMidpointTseitinStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z w : Nat) (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyMidpointTseitinStepVal R x z w input).2.1 =
      (oneHighFamilyMidpointTseitinStep x z w (input.1, input.2.1)).2 := by
  rcases input with ⟨ts, st, val⟩
  let ta : OneHighFamilyAtom := .midpoint (min x z) w (max x z)
  generalize hv₁ : oneHighFamilyAtomIdVal R ta (st, val) = out₁
  rcases out₁ with ⟨t, acc₁⟩
  have hid₁ := oneHighFamilyAtomIdVal_id R ta st val
  have hst₁ := oneHighFamilyAtomIdVal_state R ta st val
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
    (.edge (min w z) (max w z)) acc₂ = out₃
  rcases out₃ with ⟨ewz, acc₃⟩
  have hid₃ := oneHighFamilyAtomIdVal_id R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2
  have hst₃ := oneHighFamilyAtomIdVal_state R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2
  rw [hv₃] at hid₃ hst₃
  have hout₁ : oneHighFamilyAtomId ta st = (t, acc₁.1) := by
    apply Prod.ext
    · exact hid₁.symm
    · exact hst₁.symm
  have hout₂ : oneHighFamilyEdgeId x w acc₁.1 = (exw, acc₂.1) := by
    apply Prod.ext
    · exact hid₂.symm
    · exact hst₂.symm
  have hout₃ : oneHighFamilyEdgeId w z acc₂.1 = (ewz, acc₃.1) := by
    apply Prod.ext
    · exact hid₃.symm
    · exact hst₃.symm
  simp [oneHighFamilyMidpointTseitinStepVal,
    oneHighFamilyMidpointTseitinStep, oneHighFamilyEdgeIdVal,
    oneHighFamilyMidpointAtomId, ta, hv₁, hv₂, hv₃,
    hout₁, hout₂, hout₃, oneHighFamilyEmitVal]

theorem oneHighFamilyMidpointTseitinStepVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z w : Nat) (input : Array Int × OneHighFamilyValState) :
    let out := oneHighFamilyMidpointTseitinStepVal R x z w input
    let raw := oneHighFamilyMidpointTseitinStep x z w (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  constructor
  · rcases input with ⟨ts, st, val⟩
    let ta : OneHighFamilyAtom := .midpoint (min x z) w (max x z)
    generalize hv : oneHighFamilyAtomIdVal R ta (st, val) = outVal
    rcases outVal with ⟨t, acc₁⟩
    generalize hg : oneHighFamilyAtomId ta st = out
    rcases out with ⟨tg, st₁⟩
    have hid := oneHighFamilyAtomIdVal_id R ta st val
    rw [hv, hg] at hid
    dsimp at hid
    subst tg
    generalize hv₂ : oneHighFamilyAtomIdVal R
      (.edge (min x w) (max x w)) acc₁ = outv₂
    rcases outv₂ with ⟨exw, acc₂⟩
    generalize hv₃ : oneHighFamilyAtomIdVal R
      (.edge (min w z) (max w z)) acc₂ = outv₃
    rcases outv₃ with ⟨ewz, acc₃⟩
    generalize hg₂ : oneHighFamilyEdgeId x w st₁ = outg₂
    rcases outg₂ with ⟨exwg, st₂⟩
    generalize hg₃ : oneHighFamilyEdgeId w z st₂ = outg₃
    rcases outg₃ with ⟨ewzg, st₃⟩
    simp [oneHighFamilyMidpointTseitinStepVal,
      oneHighFamilyMidpointTseitinStep, oneHighFamilyMidpointAtomId,
      oneHighFamilyEdgeIdVal, ta, hv, hg, hv₂, hv₃, hg₂, hg₃]
  · exact oneHighFamilyMidpointTseitinStepVal_state R x z w input

theorem oneHighFamilyCollectMidpointsVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (ws : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let out := ws.foldl (fun input w =>
      oneHighFamilyMidpointTseitinStepVal R x z w input) input
    let raw := ws.foldl (fun input w =>
      oneHighFamilyMidpointTseitinStep x z w input) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction ws generalizing input with
  | nil => simp
  | cons w ws ih =>
      simp only [List.foldl_cons]
      have hp := oneHighFamilyMidpointTseitinStepVal_projection R x z w input
      have hi := ih (oneHighFamilyMidpointTseitinStepVal R x z w input)
      rcases hp with ⟨hvars, hst⟩
      simpa [hvars, hst] using hi

theorem oneHighFamilyMidpointTseitinStepVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x z w : Nat} (hx : x < 40) (hz : z < 40) (hw : w < 40)
    (hxz : x < z) {ts : Array Int} {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyMidpointTseitinStepVal R x z w (ts, acc)).2 := by
  simp only [oneHighFamilyMidpointTseitinStepVal,
    oneHighFamilyEdgeIdVal]
  let ta : OneHighFamilyAtom := .midpoint (min x z) w (max x z)
  generalize h₁ : oneHighFamilyAtomIdVal R ta acc = out₁
  rcases out₁ with ⟨t, acc₁⟩
  have hs₁ := oneHighFamilyAtomIdVal_semanticSound R hacc ta
  rw [h₁] at hs₁
  have hr₁ := oneHighFamilyAtomIdVal_result R ta acc.1 acc.2
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
    (.edge (min w z) (max w z)) acc₂ = out₃
  rcases out₃ with ⟨ewz, acc₃⟩
  have hs₃ := oneHighFamilyAtomIdVal_semanticSound R hs₂
    (.edge (min w z) (max w z))
  rw [h₃] at hs₃
  have hr₃ := oneHighFamilyAtomIdVal_result R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2
  rw [h₃] at hr₃
  dsimp at hr₃
  have ht₂ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hr₁.1
  rw [h₂] at ht₂
  have ht₃ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2 ht₂
  rw [h₃] at ht₃
  have he₃ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2 hr₂.1
  rw [h₃] at he₃
  have htVal : acc₃.2 t = decide
      (R.Adj (⟨x, hx⟩ : Fin 40) ⟨w, hw⟩ ∧
        R.Adj (⟨w, hw⟩ : Fin 40) ⟨z, hz⟩) := by
    rw [hs₃.named ta t ht₃]
    simp [ta, oneHighFamilyAtomValue, oneHighFamilyTAtom, hx, hz, hw,
      min_eq_left (Nat.le_of_lt hxz), max_eq_right (Nat.le_of_lt hxz)]
  have hexwVal : acc₃.2 exw =
      decide (R.Adj (⟨x, hx⟩ : Fin 40) ⟨w, hw⟩) :=
    (hs₃.named _ exw he₃).trans (oneHighFamilyAtomValue_edge R hx hw)
  have hewzVal : acc₃.2 ewz =
      decide (R.Adj (⟨w, hw⟩ : Fin 40) ⟨z, hz⟩) :=
    hr₃.2.trans (oneHighFamilyAtomValue_edge R hw hz)
  have hte₁ : acc₃.2 t = true → acc₃.2 exw = true := by
    rw [htVal, hexwVal]
    simp only [decide_eq_true_eq]
    tauto
  have hte₂ : acc₃.2 t = true → acc₃.2 ewz = true := by
    rw [htVal, hewzVal]
    simp only [decide_eq_true_eq]
    tauto
  have heet : acc₃.2 exw = true → acc₃.2 ewz = true →
      acc₃.2 t = true := by
    rw [htVal, hexwVal, hewzVal]
    simp only [decide_eq_true_eq]
    tauto
  let acc₄ := (oneHighFamilyEmitVal [-(t : Int), (exw : Int)] acc₃).2
  have hs₄ : OneHighFamilySemanticSound R acc₄ := by
    apply oneHighFamilyEmitVal_semanticSound R hs₃
    · exact dimacsClauseSatisfied_negative_positive
        (hs₃.ids.id_bounds _ he₃).1 hte₁
    · exact dimacsClauseBounded_negative_positive
        (hs₃.ids.id_bounds _ ht₃).2
        (hs₃.ids.id_bounds _ he₃).2
  let acc₅ := (oneHighFamilyEmitVal [-(t : Int), (ewz : Int)] acc₄).2
  have hs₅ : OneHighFamilySemanticSound R acc₅ := by
    apply oneHighFamilyEmitVal_semanticSound R hs₄
    · simpa [acc₄, oneHighFamilyEmitVal] using
        dimacsClauseSatisfied_negative_positive
          (hs₃.ids.id_bounds _ hr₃.1).1 hte₂
    · exact dimacsClauseBounded_negative_positive
        (hs₄.ids.id_bounds _ (by exact ht₃)).2
        (hs₄.ids.id_bounds _ (by exact hr₃.1)).2
  simp only [h₂, h₃]
  apply oneHighFamilyEmitVal_semanticSound R hs₅
  · simpa [acc₄, acc₅, oneHighFamilyEmitVal] using
      dimacsClauseSatisfied_positive_negative_pair
        (hs₃.ids.id_bounds _ ht₃).1 heet
  · exact dimacsClauseBounded_positive_negative_pair
      (hs₅.ids.id_bounds _ (by exact ht₃)).2
      (hs₅.ids.id_bounds _ (by exact he₃)).2
      (hs₅.ids.id_bounds _ (by exact hr₃.1)).2

theorem oneHighFamilyMidpointTseitinStepVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z w : Nat) {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyMidpointTseitinStepVal R x z w input).2.1.ids := by
  rcases input with ⟨ts, acc⟩
  let ta : OneHighFamilyAtom := .midpoint (min x z) w (max x z)
  simp only [oneHighFamilyMidpointTseitinStepVal, oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R ta acc = out₁
  rcases out₁ with ⟨t, acc₁⟩
  have hm₁ := oneHighFamilyAtomIdVal_old_mem R ta acc.1 acc.2 hmem
  rw [h₁] at hm₁
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  have hm₂ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hm₁
  rw [h₂] at hm₂
  generalize h₃ : oneHighFamilyAtomIdVal R
    (.edge (min w z) (max w z)) acc₂ = out₃
  rcases out₃ with ⟨ewz, acc₃⟩
  have hm₃ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2 hm₂
  rw [h₃] at hm₃
  simp only [h₁, h₂, h₃]
  exact hm₃

theorem oneHighFamilyCollectMidpointsVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (ws : List Nat)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (ws.foldl (fun input w =>
      oneHighFamilyMidpointTseitinStepVal R x z w input) input).2.1.ids := by
  induction ws generalizing input with
  | nil => exact hmem
  | cons w ws ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyMidpointTseitinStepVal_old_mem R x z w hmem)

structure OneHighFamilyCollectedMidpointsMatch
    (x z : Nat) (ws : List Nat)
    (input : Array Int × OneHighFamilyValState) where
  ids : List Nat
  vars_eq : input.1.toList = List.map (fun id : Nat => (id : Int)) ids
  aligned : List.Forall₂ (fun w id =>
    ((.midpoint (min x z) w (max x z)), id) ∈ input.2.1.ids) ws ids

def oneHighFamilyCollectedMidpointsMatch_empty
    (x z : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedMidpointsMatch x z [] (#[], acc) where
  ids := []
  vars_eq := rfl
  aligned := .nil

noncomputable def oneHighFamilyCollectedMidpointsMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x z w : Nat} {ws : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedMidpointsMatch x z ws input) :
    OneHighFamilyCollectedMidpointsMatch x z (ws ++ [w])
      (oneHighFamilyMidpointTseitinStepVal R x z w input) := by
  rcases input with ⟨ts, acc⟩
  let ta : OneHighFamilyAtom := .midpoint (min x z) w (max x z)
  simp only [oneHighFamilyMidpointTseitinStepVal,
    oneHighFamilyEdgeIdVal]
  generalize h₁ : oneHighFamilyAtomIdVal R ta acc = out₁
  rcases out₁ with ⟨t, acc₁⟩
  generalize h₂ : oneHighFamilyAtomIdVal R
    (.edge (min x w) (max x w)) acc₁ = out₂
  rcases out₂ with ⟨exw, acc₂⟩
  generalize h₃ : oneHighFamilyAtomIdVal R
    (.edge (min w z) (max w z)) acc₂ = out₃
  rcases out₃ with ⟨ewz, acc₃⟩
  have hr₁ := oneHighFamilyAtomIdVal_result R ta acc.1 acc.2
  rw [h₁] at hr₁
  dsimp at hr₁
  have ht₂ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hr₁.1
  rw [h₂] at ht₂
  have ht₃ := oneHighFamilyAtomIdVal_old_mem R
    (.edge (min w z) (max w z)) acc₂.1 acc₂.2 ht₂
  rw [h₃] at ht₃
  simp only [h₁, h₂, h₃]
  refine ⟨h.ids ++ [t], ?_, ?_⟩
  · rw [Array.toList_push, h.vars_eq]
    simp
  · change List.Forall₂ (fun w' id =>
        ((.midpoint (min x z) w' (max x z)), id) ∈ acc₃.1.ids)
        (ws ++ [w]) (h.ids ++ [t])
    have hold : List.Forall₂ (fun w' id =>
        ((.midpoint (min x z) w' (max x z)), id) ∈ acc₃.1.ids)
        ws h.ids := by
      apply h.aligned.imp
      intro w' id hm
      have hm₁ := oneHighFamilyAtomIdVal_old_mem R ta acc.1 acc.2 hm
      rw [h₁] at hm₁
      have hm₂ := oneHighFamilyAtomIdVal_old_mem R
        (.edge (min x w) (max x w)) acc₁.1 acc₁.2 hm₁
      rw [h₂] at hm₂
      have hm₃ := oneHighFamilyAtomIdVal_old_mem R
        (.edge (min w z) (max w z)) acc₂.1 acc₂.2 hm₂
      rw [h₃] at hm₃
      exact hm₃
    apply listForall₂_append_singleton hold
    exact ht₃

noncomputable def oneHighFamilyCollectMidpointsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (ws : List Nat) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  ws.foldl (fun input w =>
    oneHighFamilyMidpointTseitinStepVal R x z w input) (#[], acc)

noncomputable def oneHighFamilyCollectMidpointsVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Nat) (ws : List Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedMidpointsMatch x z ws
      (oneHighFamilyCollectMidpointsVal R x z ws acc) := by
  suffices ∀ pre : List Nat,
      OneHighFamilyCollectedMidpointsMatch x z pre
        (pre.foldl (fun input w =>
          oneHighFamilyMidpointTseitinStepVal R x z w input) (#[], acc)) by
    exact this ws
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact oneHighFamilyCollectedMidpointsMatch_empty x z acc
  | append_singleton pre w ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact oneHighFamilyCollectedMidpointsMatch_push R ih

theorem oneHighFamilyCollectMidpointsVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x z : Nat} (hx : x < 40) (hz : z < 40) (hxz : x < z)
    (ws : List Nat) (hws : ∀ w ∈ ws, w < 40)
    {ts : Array Int} {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (ws.foldl (fun input w =>
        oneHighFamilyMidpointTseitinStepVal R x z w input) (ts, acc)).2 := by
  induction ws generalizing ts acc with
  | nil => exact hacc
  | cons w ws ih =>
      simp only [oneHighFamilyCollectMidpointsVal, List.foldl_cons]
      apply ih
      · intro w' hw'
        exact hws w' (by simp [hw'])
      · exact oneHighFamilyMidpointTseitinStepVal_semanticSound R
          hx hz (hws w (by simp)) hxz (ts := ts) hacc

theorem oneHighFamilyAtomValue_midpoint
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x z w : Nat} (hx : x < 40) (hz : z < 40) (hw : w < 40)
    (hxz : x < z) :
    oneHighFamilyAtomValue R (.midpoint (min x z) w (max x z)) =
      @decide (oneHighFamilyTAtom R
        (⟨x, hx⟩ : Fin 40) ⟨w, hw⟩ ⟨z, hz⟩)
        (Classical.propDecidable _) := by
  classical
  simp [oneHighFamilyAtomValue, oneHighFamilyTAtom, hx, hz, hw,
    min_eq_left (Nat.le_of_lt hxz), max_eq_right (Nat.le_of_lt hxz)]

theorem oneHighFamilyCollectedMidpoints_exists_true_iff
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {x z : Nat} {ws : List Nat}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedMidpointsMatch x z ws input)
    (hs : OneHighFamilySemanticSound R input.2) :
    (∃ id ∈ h.ids, input.2.2 id = true) ↔
      ∃ w ∈ ws,
        oneHighFamilyAtomValue R
          (.midpoint (min x z) w (max x z)) = true := by
  constructor
  · rintro ⟨id, hid, hval⟩
    rcases listForall₂_exists_left_of_mem h.aligned hid with
      ⟨w, hwmem, hatom⟩
    refine ⟨w, hwmem, ?_⟩
    exact (hs.named _ id hatom).symm.trans hval
  · rintro ⟨w, hwmem, hval⟩
    rcases listForall₂_exists_right_of_mem h.aligned hwmem with
      ⟨id, hid, hatom⟩
    refine ⟨id, hid, ?_⟩
    exact (hs.named _ id hatom).trans hval

theorem oneHighFamilyPairedMidpoints_mem
    {bi bj w : Nat} (hw : w ∈ oneHighFamilyPairedMidpoints bi bj) :
    w < 40 ∧ w / 5 ≠ bi ∧ w / 5 ≠ bj := by
  have hf := List.mem_filter.mp hw
  refine ⟨List.mem_range.mp hf.1, ?_⟩
  exact of_decide_eq_true hf.2

theorem oneHighFamilyPairedMidpoints_mem_iff
    (b : Fin 8) {w : Nat} :
    w ∈ oneHighFamilyPairedMidpoints b.val (oneHighStandardMate b).val ↔
      ∃ hw : w < 40, (⟨w, hw⟩ : Fin 40) ∈ oneHighFamilyMidpoints b := by
  constructor
  · intro hw
    have hp := oneHighFamilyPairedMidpoints_mem hw
    refine ⟨hp.1, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro heq
      exact hp.2.1 (congrArg Fin.val heq)
    · intro heq
      exact hp.2.2 (congrArg Fin.val heq)
  · rintro ⟨hw40, hw⟩
    have hp := Finset.mem_filter.mp hw
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hw40, ?_⟩
    apply decide_eq_true
    constructor
    · intro heq
      exact hp.2.1 (Fin.ext heq)
    · intro heq
      exact hp.2.2 (Fin.ext heq)

def oneHighFamilyEmitCommonPairsVal (c : Nat) (ids : List Nat)
    (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  List.foldl (fun (acc : OneHighFamilyValState) (id : Nat) =>
    (oneHighFamilyEmitVal [-(id : Int), (c : Int)] acc).2) acc ids

@[simp] theorem oneHighFamilyEmitCommonPairsVal_ids
    (c : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitCommonPairsVal c ids acc).1.ids = acc.1.ids := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitCommonPairsVal c ids
        (oneHighFamilyEmitVal [-(id : Int), (c : Int)] acc).2).1.ids = _
      rw [ih]
      rfl

@[simp] theorem oneHighFamilyEmitCommonPairsVal_value
    (c : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitCommonPairsVal c ids acc).2 = acc.2 := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitCommonPairsVal c ids
        (oneHighFamilyEmitVal [-(id : Int), (c : Int)] acc).2).2 = _
      rw [ih]
      rfl

theorem oneHighFamilyEmitCommonPairsVal_state
    (c : Nat) (ids : List Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyEmitCommonPairsVal c ids acc).1 =
      List.foldl (fun (st : OneHighFamilyGenState) (id : Nat) =>
        (oneHighFamilyEmit [-(id : Int), (c : Int)] st).2) acc.1 ids := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
      change (oneHighFamilyEmitCommonPairsVal c ids
        (oneHighFamilyEmitVal [-(id : Int), (c : Int)] acc).2).1 = _
      rw [ih]
      rfl

theorem oneHighFamilyEmitCommonPairsVal_semanticSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {c : Nat} {ids : List Nat} {acc : OneHighFamilyValState}
    (h : OneHighFamilySemanticSound R acc)
    (hc : ∃ atom, (atom, c) ∈ acc.1.ids)
    (hids : ∀ id ∈ ids, ∃ atom, (atom, id) ∈ acc.1.ids)
    (himp : ∀ id ∈ ids, acc.2 id = true → acc.2 c = true) :
    OneHighFamilySemanticSound R
      (oneHighFamilyEmitCommonPairsVal c ids acc) := by
  induction ids generalizing acc with
  | nil => exact h
  | cons id ids ih =>
      simp only [oneHighFamilyEmitCommonPairsVal, List.foldl_cons]
      let next := (oneHighFamilyEmitVal [-(id : Int), (c : Int)] acc).2
      have hid := hids id (by simp)
      have hs : OneHighFamilySemanticSound R next := by
        apply oneHighFamilyEmitVal_semanticSound R h
        · exact dimacsClauseSatisfied_negative_positive
            (h.ids.id_bounds _ hc.choose_spec).1 (himp id (by simp))
        · exact dimacsClauseBounded_negative_positive
            (h.ids.id_bounds _ hid.choose_spec).2
            (h.ids.id_bounds _ hc.choose_spec).2
      apply ih hs
      · rcases hc with ⟨atom, hm⟩
        exact ⟨atom, by exact hm⟩
      · intro id' hid'
        exact hids id' (by simp [hid'])
      · intro id' hid'
        simpa [next, oneHighFamilyEmitVal] using himp id' (by simp [hid'])

noncomputable def oneHighFamilyCommonTseitinStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj x z : Nat) (input : Array Int × OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  let (cs, acc) := input
  let mids := oneHighFamilyPairedMidpoints bi bj
  let tsInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  let hm := oneHighFamilyCollectMidpointsVal_match R x z mids acc
  let (c, acc) := oneHighFamilyAtomIdVal R
    (.common (min x z) (max x z)) tsInput.2
  let acc := (oneHighFamilyEmitVal
    (-(c : Int) :: List.map (fun id : Nat => (id : Int)) hm.ids) acc).2
  let acc := oneHighFamilyEmitCommonPairsVal c hm.ids acc
  (cs.push (c : Int), acc)

theorem oneHighFamilyCommonTseitinStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (b : Fin 8) {x z : Nat} (hx : x < 40) (hz : z < 40) (hxz : x < z)
    (hxBlock : Fin.divNat (m := 8) (n := 5) (⟨x, hx⟩ : Fin 40) = b)
    (hzBlock : Fin.divNat (m := 8) (n := 5) (⟨z, hz⟩ : Fin 40) =
      oneHighStandardMate b)
    {cs : Array Int} {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyCommonTseitinStepVal R b.val
        (oneHighStandardMate b).val x z (cs, acc)).2 := by
  classical
  let mids := oneHighFamilyPairedMidpoints b.val
    (oneHighStandardMate b).val
  have hmidsBound : ∀ w ∈ mids, w < 40 := by
    intro w hw
    exact (oneHighFamilyPairedMidpoints_mem hw).1
  let tsInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  let hm := oneHighFamilyCollectMidpointsVal_match R x z mids acc
  have hsInput : OneHighFamilySemanticSound R tsInput.2 := by
    exact oneHighFamilyCollectMidpointsVal_semanticSound R hx hz hxz mids
      hmidsBound (ts := #[]) hacc
  let ca : OneHighFamilyAtom := .common (min x z) (max x z)
  generalize hca : oneHighFamilyAtomIdVal R ca tsInput.2 = out
  rcases out with ⟨c, accC⟩
  have hsC := oneHighFamilyAtomIdVal_semanticSound R hsInput ca
  rw [hca] at hsC
  have hrC := oneHighFamilyAtomIdVal_result R ca tsInput.2.1 tsInput.2.2
  rw [hca] at hrC
  dsimp at hrC
  let hmC : OneHighFamilyCollectedMidpointsMatch x z mids
      (tsInput.1, accC) := {
    ids := hm.ids
    vars_eq := hm.vars_eq
    aligned := hm.aligned.imp (by
      intro w id hmem
      have hold := oneHighFamilyAtomIdVal_old_mem R ca
        tsInput.2.1 tsInput.2.2 hmem
      rw [hca] at hold
      exact hold) }
  have hmin : (⟨min x z, by omega⟩ : Fin 40) = ⟨x, hx⟩ := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt hxz)
  have hmax : (⟨max x z, by omega⟩ : Fin 40) = ⟨z, hz⟩ := by
    apply Fin.ext
    exact max_eq_right (Nat.le_of_lt hxz)
  have hcVal : accC.2 c = decide
      (oneHighFamilyCAtom R b (⟨x, hx⟩ : Fin 40) ⟨z, hz⟩) := by
    rw [hrC.2]
    simp only [ca, oneHighFamilyAtomValue, dif_pos (by omega : min x z < 40),
      dif_pos (by omega : max x z < 40), oneHighFamilyCAtom,
      oneHighEncodedCommonPairBlock, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    rw [hmin, hmax]
    simp [hxBlock, hzBlock]
  have hiff : accC.2 c = true ↔ ∃ id ∈ hm.ids, accC.2 id = true := by
    rw [hcVal]
    simp only [decide_eq_true_eq]
    rw [oneHighFamily_cAtom_iff_exists_tAtom hc.relation b
      (⟨x, hx⟩ : Fin 40) ⟨z, hz⟩ hxBlock hzBlock]
    rw [oneHighFamilyCollectedMidpoints_exists_true_iff R hmC hsC]
    constructor
    · rintro ⟨w, hwFin, ht⟩
      have hwList := (oneHighFamilyPairedMidpoints_mem_iff b).mpr
        ⟨w.2, by simpa using hwFin⟩
      refine ⟨w.val, hwList, ?_⟩
      rw [oneHighFamilyAtomValue_midpoint R hx hz w.2 hxz]
      exact decide_eq_true ht
    · rintro ⟨w, hwList, ht⟩
      rcases (oneHighFamilyPairedMidpoints_mem_iff b).mp hwList with
        ⟨hw40, hwFin⟩
      refine ⟨(⟨w, hw40⟩ : Fin 40), hwFin, ?_⟩
      rw [oneHighFamilyAtomValue_midpoint R hx hz hw40 hxz] at ht
      exact of_decide_eq_true ht
  have hids : ∀ id ∈ hm.ids,
      ∃ atom, (atom, id) ∈ accC.1.ids := by
    intro id hid
    rcases listForall₂_exists_left_of_mem hmC.aligned hid with
      ⟨w, _, hatom⟩
    exact ⟨.midpoint (min x z) w (max x z), hatom⟩
  let accOr := (oneHighFamilyEmitVal
    (-(c : Int) :: List.map (fun id : Nat => (id : Int)) hm.ids) accC).2
  have hsOr : OneHighFamilySemanticSound R accOr := by
    apply oneHighFamilyEmitVal_semanticSound R hsC
    · apply dimacsClauseSatisfied_negative_positive_ids
      · exact (hsC.ids.id_bounds _ hrC.1).1
      · intro id hid
        exact (hsC.ids.id_bounds _ (hids id hid).choose_spec).1
      · exact hiff.mp
    · apply dimacsClauseBounded_negative_positive_ids
      · exact (hsC.ids.id_bounds _ hrC.1).2
      · intro id hid
        exact (hsC.ids.id_bounds _ (hids id hid).choose_spec).2
  simp only [oneHighFamilyCommonTseitinStepVal,
    oneHighFamilyCollectMidpointsVal]
  dsimp [ca, tsInput, mids, oneHighFamilyCollectMidpointsVal] at hca
  rw [hca]
  change OneHighFamilySemanticSound R
    (oneHighFamilyEmitCommonPairsVal c hm.ids accOr)
  apply oneHighFamilyEmitCommonPairsVal_semanticSound R hsOr
  · exact ⟨ca, by exact hrC.1⟩
  · exact hids
  · intro id hid ht
    have hvEq : accOr.2 = accC.2 := by
      exact oneHighFamilyEmitVal_value _ _ _
    rw [hvEq] at ht ⊢
    exact hiff.mpr ⟨id, hid, ht⟩

theorem oneHighFamilyCommonTseitinStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj x z : Nat) (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyCommonTseitinStepVal R bi bj x z input).2.1 =
      (oneHighFamilyCommonTseitinStep bi bj x z (input.1, input.2.1)).2 := by
  rcases input with ⟨cs, acc⟩
  let mids := oneHighFamilyPairedMidpoints bi bj
  let tsInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  let raw := mids.foldl (fun input w =>
    oneHighFamilyMidpointTseitinStep x z w input) (#[], acc.1)
  have hp := oneHighFamilyCollectMidpointsVal_projection R x z mids (#[], acc)
  change tsInput.1 = raw.1 ∧ tsInput.2.1 = raw.2 at hp
  generalize hraw : raw = rawOut
  rcases rawOut with ⟨rawTs, rawSt⟩
  rw [hraw] at hp
  rcases hp with ⟨hTs, hSt⟩
  let ca : OneHighFamilyAtom := .common (min x z) (max x z)
  generalize hv : oneHighFamilyAtomIdVal R ca tsInput.2 = outVal
  rcases outVal with ⟨c, accC⟩
  generalize hg : oneHighFamilyCommonAtomId x z rawSt = out
  rcases out with ⟨cg, stC⟩
  have hid := oneHighFamilyAtomIdVal_id R ca tsInput.2.1 tsInput.2.2
  have hstate := oneHighFamilyAtomIdVal_state R ca tsInput.2.1 tsInput.2.2
  rw [hv] at hid hstate
  have hg' : oneHighFamilyAtomId ca rawSt = (cg, stC) := by
    simpa [oneHighFamilyCommonAtomId, ca] using hg
  rw [hSt, hg'] at hid hstate
  dsimp at hid hstate
  subst cg
  let hm := oneHighFamilyCollectMidpointsVal_match R x z mids acc
  have hvars : rawTs.toList =
      List.map (fun id : Nat => (id : Int)) hm.ids := by
    exact (congrArg Array.toList hTs).symm.trans hm.vars_eq
  simp only [oneHighFamilyCommonTseitinStepVal,
    oneHighFamilyCollectMidpointsVal, mids]
  dsimp [ca, tsInput, mids, oneHighFamilyCollectMidpointsVal] at hv
  rw [hv]
  rw [oneHighFamilyEmitCommonPairsVal_state]
  rw [oneHighFamilyEmitVal_state]
  rw [hstate]
  change _ = (let (ts, st) := raw
    let (c, st) := oneHighFamilyCommonAtomId x z st
    let st := (oneHighFamilyEmit (-(c : Int) :: ts.toList) st).2
    let st := ts.foldl
      (fun st t => (oneHighFamilyEmit [-t, (c : Int)] st).2) st
    (cs.push (c : Int), st)).2
  rw [hraw]
  dsimp only
  rw [hg]
  dsimp only
  change List.foldl (fun st (id : Nat) =>
      (oneHighFamilyEmit [-(id : Int), (c : Int)] st).2)
      (oneHighFamilyEmit (-(c : Int) ::
        List.map (fun id : Nat => (id : Int)) hm.ids) stC).2 hm.ids =
    rawTs.foldl (fun st t =>
      (oneHighFamilyEmit [-t, (c : Int)] st).2)
      (oneHighFamilyEmit (-(c : Int) :: rawTs.toList) stC).2
  rw [← Array.foldl_toList]
  rw [hvars]
  rw [List.foldl_map]

structure OneHighFamilyCollectedCommonsMatch
    (pairs : List (Nat × Nat))
    (input : Array Int × OneHighFamilyValState) where
  ids : List Nat
  vars_eq : input.1.toList = List.map (fun id : Nat => (id : Int)) ids
  aligned : List.Forall₂ (fun p id =>
    ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈ input.2.1.ids)
    pairs ids

def oneHighFamilyCollectedCommonsMatch_empty
    (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedCommonsMatch [] (#[], acc) where
  ids := []
  vars_eq := rfl
  aligned := .nil

noncomputable def oneHighFamilyCollectedCommonsMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {bi bj x z : Nat} {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch (pairs ++ [(x, z)])
      (oneHighFamilyCommonTseitinStepVal R bi bj x z input) := by
  rcases input with ⟨cs, acc⟩
  let mids := oneHighFamilyPairedMidpoints bi bj
  generalize hmids : oneHighFamilyCollectMidpointsVal R x z mids acc = tsInput
  rcases tsInput with ⟨ts, accTs⟩
  let ca : OneHighFamilyAtom := .common (min x z) (max x z)
  generalize hca : oneHighFamilyAtomIdVal R ca accTs = out
  rcases out with ⟨c, accC⟩
  have hrC := oneHighFamilyAtomIdVal_result R ca accTs.1 accTs.2
  rw [hca] at hrC
  dsimp at hrC
  have hold : List.Forall₂ (fun p id =>
      ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈ accC.1.ids)
      pairs h.ids := by
    apply h.aligned.imp
    intro p id hmem
    have hm := oneHighFamilyCollectMidpointsVal_old_mem R x z mids
      (input := (#[], acc)) hmem
    change ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈
      (oneHighFamilyCollectMidpointsVal R x z mids acc).2.1.ids at hm
    rw [hmids] at hm
    have hc := oneHighFamilyAtomIdVal_old_mem R ca accTs.1 accTs.2 hm
    rw [hca] at hc
    exact hc
  simp only [oneHighFamilyCommonTseitinStepVal,
    oneHighFamilyCollectMidpointsVal]
  dsimp [mids, oneHighFamilyCollectMidpointsVal] at hmids
  dsimp [ca] at hca
  simp only [hmids, hca]
  refine ⟨h.ids ++ [c], ?_, ?_⟩
  · rw [Array.toList_push, h.vars_eq]
    simp
  · rw [oneHighFamilyEmitCommonPairsVal_ids]
    change List.Forall₂ (fun p id =>
        ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈ accC.1.ids)
        (pairs ++ [(x, z)]) (h.ids ++ [c])
    exact listForall₂_append_singleton hold hrC.1

def oneHighFamilyCommonPairs (bi bj : Nat) : List (Nat × Nat) :=
  (oneHighFamilyBlockVertices bi).foldl (fun pairs x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun pairs z => pairs ++ [(x, z)]) pairs) []

noncomputable def oneHighFamilyCollectCommonsVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj : Nat) (acc : OneHighFamilyValState) :
    Array Int × OneHighFamilyValState :=
  (oneHighFamilyBlockVertices bi).foldl (fun input x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun input z => oneHighFamilyCommonTseitinStepVal R bi bj x z input)
      input) (#[], acc)

noncomputable def oneHighFamilyCollectCommonsInner_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj x : Nat) (zs : List Nat) {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch
      (zs.foldl (fun pairs z => pairs ++ [(x, z)]) pairs)
      (zs.foldl (fun input z =>
        oneHighFamilyCommonTseitinStepVal R bi bj x z input) input) := by
  induction zs generalizing pairs input with
  | nil => exact h
  | cons z zs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyCollectedCommonsMatch_push R h)

noncomputable def oneHighFamilyCollectCommonsOuter_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj : Nat) (xs : List Nat) {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch
      (xs.foldl (fun pairs x =>
        (oneHighFamilyBlockVertices bj).foldl
          (fun pairs z => pairs ++ [(x, z)]) pairs) pairs)
      (xs.foldl (fun input x =>
        (oneHighFamilyBlockVertices bj).foldl (fun input z =>
          oneHighFamilyCommonTseitinStepVal R bi bj x z input) input) input) := by
  induction xs generalizing pairs input with
  | nil => exact h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyCollectCommonsInner_match R bi bj x _ h)

noncomputable def oneHighFamilyCollectCommonsVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj : Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedCommonsMatch (oneHighFamilyCommonPairs bi bj)
      (oneHighFamilyCollectCommonsVal R bi bj acc) := by
  exact oneHighFamilyCollectCommonsOuter_match R bi bj _
    (oneHighFamilyCollectedCommonsMatch_empty acc)

theorem oneHighStandardMate_even_pair (pair : Nat) (hpair : pair < 4) :
    oneHighStandardMate (⟨2 * pair, by omega⟩ : Fin 8) =
      (⟨2 * pair + 1, by omega⟩ : Fin 8) := by
  interval_cases pair <;> native_decide +revert

theorem oneHighFamilyCollectCommonsInner_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (pair : Nat) (hpair : pair < 4)
    {x : Nat} (hxmem : x ∈ oneHighFamilyBlockVertices (2 * pair))
    (zs : List Nat)
    (hzs : ∀ z ∈ zs,
      z ∈ oneHighFamilyBlockVertices (2 * pair + 1))
    (input : Array Int × OneHighFamilyValState)
    (hinput : OneHighFamilySemanticSound R input.2) :
    OneHighFamilySemanticSound R
      (zs.foldl (fun input z =>
        oneHighFamilyCommonTseitinStepVal R (2 * pair)
          (2 * pair + 1) x z input) input).2 := by
  have hx := oneHighFamilyBlockVertices_mem (by omega) hxmem
  let b : Fin 8 := ⟨2 * pair, by omega⟩
  have hmate : oneHighStandardMate b =
      (⟨2 * pair + 1, by omega⟩ : Fin 8) :=
    oneHighStandardMate_even_pair pair hpair
  induction zs generalizing input with
  | nil => exact hinput
  | cons z zs ih =>
      simp only [List.foldl_cons]
      have hzmem := hzs z (by simp)
      have hz := oneHighFamilyBlockVertices_mem (by omega) hzmem
      have hxz : x < z := by omega
      have hxBlock : Fin.divNat (m := 8) (n := 5)
          (⟨x, hx.1⟩ : Fin 40) = b := by
        apply Fin.ext
        simpa [Fin.divNat] using hx.2
      have hzBlock : Fin.divNat (m := 8) (n := 5)
          (⟨z, hz.1⟩ : Fin 40) = oneHighStandardMate b := by
        rw [hmate]
        apply Fin.ext
        simpa [Fin.divNat] using hz.2
      apply ih
      · intro z' hz'
        exact hzs z' (by simp [hz'])
      · simpa [b, hmate] using
          (oneHighFamilyCommonTseitinStepVal_semanticSound a R hc b
            (cs := input.1) (acc := input.2)
            hx.1 hz.1 hxz hxBlock hzBlock hinput)

theorem oneHighFamilyCollectCommonsVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (pair : Nat) (hpair : pair < 4)
    (acc : OneHighFamilyValState)
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyCollectCommonsVal R (2 * pair) (2 * pair + 1) acc).2 := by
  unfold oneHighFamilyCollectCommonsVal
  have outer : ∀ (xs : List Nat)
      (input : Array Int × OneHighFamilyValState),
      (∀ x ∈ xs, x ∈ oneHighFamilyBlockVertices (2 * pair)) →
      OneHighFamilySemanticSound R input.2 →
      OneHighFamilySemanticSound R
        (xs.foldl (fun input x =>
          (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
            (fun input z => oneHighFamilyCommonTseitinStepVal R
              (2 * pair) (2 * pair + 1) x z input) input) input).2 := by
    intro xs
    induction xs with
    | nil => intro input _ hinput; exact hinput
    | cons x xs ih =>
        intro input hmem hinput
        simp only [List.foldl_cons]
        apply ih
        · intro x' hx'
          exact hmem x' (by simp [hx'])
        · exact oneHighFamilyCollectCommonsInner_semanticSound a R hc pair
            hpair (hmem x (by simp)) _ (fun z hz => hz) input hinput
  exact outer _ (#[], acc) (fun x hx => hx) hacc

theorem oneHighFamilyCommonTseitinStepVal_vars
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj x z : Nat) (input : Array Int × OneHighFamilyValState) :
    (oneHighFamilyCommonTseitinStepVal R bi bj x z input).1 =
      (oneHighFamilyCommonTseitinStep bi bj x z
        (input.1, input.2.1)).1 := by
  rcases input with ⟨cs, acc⟩
  let mids := oneHighFamilyPairedMidpoints bi bj
  let tsInput := oneHighFamilyCollectMidpointsVal R x z mids acc
  let raw := mids.foldl (fun input w =>
    oneHighFamilyMidpointTseitinStep x z w input) (#[], acc.1)
  have hp := oneHighFamilyCollectMidpointsVal_projection R x z mids (#[], acc)
  change tsInput.1 = raw.1 ∧ tsInput.2.1 = raw.2 at hp
  let ca : OneHighFamilyAtom := .common (min x z) (max x z)
  generalize hv : oneHighFamilyAtomIdVal R ca tsInput.2 = outVal
  rcases outVal with ⟨c, accC⟩
  generalize hg : oneHighFamilyCommonAtomId x z raw.2 = out
  rcases out with ⟨cg, stC⟩
  have hid := oneHighFamilyAtomIdVal_id R ca tsInput.2.1 tsInput.2.2
  rw [hv] at hid
  have hg' : oneHighFamilyAtomId ca raw.2 = (cg, stC) := by
    simpa [oneHighFamilyCommonAtomId, ca] using hg
  rw [hp.2, hg'] at hid
  dsimp at hid
  subst cg
  simp only [oneHighFamilyCommonTseitinStepVal,
    oneHighFamilyCollectMidpointsVal]
  dsimp [ca, tsInput, mids, oneHighFamilyCollectMidpointsVal] at hv
  rw [hv]
  change cs.push (c : Int) =
    (let (ts, st) := raw
     let (c, st) := oneHighFamilyCommonAtomId x z st
     let st := (oneHighFamilyEmit (-(c : Int) :: ts.toList) st).2
     let st := ts.foldl
       (fun st t => (oneHighFamilyEmit [-t, (c : Int)] st).2) st
     (cs.push (c : Int), st)).1
  generalize hraw : raw = rawOut
  rcases rawOut with ⟨rawTs, rawSt⟩
  rw [hraw] at hg
  simp only [hraw]
  rw [hg]

theorem oneHighFamilyCollectCommonsInner_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj x : Nat) (zs : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let valOut := zs.foldl (fun input z =>
      oneHighFamilyCommonTseitinStepVal R bi bj x z input) input
    let rawOut := zs.foldl (fun input z =>
      oneHighFamilyCommonTseitinStep bi bj x z input)
      (input.1, input.2.1)
    valOut.1 = rawOut.1 ∧ valOut.2.1 = rawOut.2 := by
  induction zs generalizing input with
  | nil => exact ⟨rfl, rfl⟩
  | cons z zs ih =>
      simp only [List.foldl_cons]
      have hv := oneHighFamilyCommonTseitinStepVal_vars R bi bj x z input
      have hs := oneHighFamilyCommonTseitinStepVal_state R bi bj x z input
      have tail := ih (oneHighFamilyCommonTseitinStepVal R bi bj x z input)
      simpa [hv, hs] using tail

theorem oneHighFamilyCollectCommonsOuter_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj : Nat) (xs : List Nat)
    (input : Array Int × OneHighFamilyValState) :
    let valOut := xs.foldl (fun input x =>
      (oneHighFamilyBlockVertices bj).foldl (fun input z =>
        oneHighFamilyCommonTseitinStepVal R bi bj x z input) input) input
    let rawOut := xs.foldl (fun input x =>
      (oneHighFamilyBlockVertices bj).foldl (fun input z =>
        oneHighFamilyCommonTseitinStep bi bj x z input) input)
      (input.1, input.2.1)
    valOut.1 = rawOut.1 ∧ valOut.2.1 = rawOut.2 := by
  induction xs generalizing input with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have inner := oneHighFamilyCollectCommonsInner_projection R bi bj x
        (oneHighFamilyBlockVertices bj) input
      have tail := ih ((oneHighFamilyBlockVertices bj).foldl
        (fun input z => oneHighFamilyCommonTseitinStepVal R bi bj x z input)
        input)
      simpa [inner.1, inner.2] using tail

theorem oneHighFamilyCollectCommonsVal_projection
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (bi bj : Nat) (acc : OneHighFamilyValState) :
    let valOut := oneHighFamilyCollectCommonsVal R bi bj acc
    let rawOut := (oneHighFamilyBlockVertices bi).foldl (fun input x =>
      (oneHighFamilyBlockVertices bj).foldl (fun input z =>
        oneHighFamilyCommonTseitinStep bi bj x z input) input) (#[], acc.1)
    valOut.1 = rawOut.1 ∧ valOut.2.1 = rawOut.2 := by
  exact oneHighFamilyCollectCommonsOuter_projection R bi bj _ (#[], acc)

theorem foldl_append_pairs_eq_append_map (x : Nat) (zs : List Nat)
    (pairs : List (Nat × Nat)) :
    zs.foldl (fun pairs z => pairs ++ [(x, z)]) pairs =
      pairs ++ zs.map (fun z => (x, z)) := by
  induction zs generalizing pairs with
  | nil => simp
  | cons z zs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      simp [List.append_assoc]

theorem oneHighFamilyCommonPairs_eq_product (bi bj : Nat) :
    oneHighFamilyCommonPairs bi bj =
      (oneHighFamilyBlockVertices bi).product
        (oneHighFamilyBlockVertices bj) := by
  unfold oneHighFamilyCommonPairs List.product
  have go : ∀ (xs zs : List Nat) (pairs : List (Nat × Nat)),
      xs.foldl (fun pairs x =>
        zs.foldl (fun pairs z => pairs ++ [(x, z)]) pairs) pairs =
        pairs ++ xs.flatMap (fun x => zs.map (Prod.mk x)) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro zs pairs
        simp only [List.foldl_cons, List.flatMap_cons]
        rw [foldl_append_pairs_eq_append_map, ih]
        simp [List.append_assoc]
  simpa using go (oneHighFamilyBlockVertices bi)
    (oneHighFamilyBlockVertices bj) []

theorem oneHighFamilyBlockVertices_nodup (b : Nat) :
    (oneHighFamilyBlockVertices b).Nodup := by
  unfold oneHighFamilyBlockVertices
  apply List.Nodup.map
  · intro a c heq
    exact Nat.add_left_cancel heq
  · exact List.nodup_range

theorem oneHighFamilyCommonPairs_nodup (bi bj : Nat) :
    (oneHighFamilyCommonPairs bi bj).Nodup := by
  rw [oneHighFamilyCommonPairs_eq_product]
  exact (oneHighFamilyBlockVertices_nodup bi).product
    (oneHighFamilyBlockVertices_nodup bj)

theorem mem_oneHighFamilyCommonPairs_iff {bi bj x z : Nat} :
    (x, z) ∈ oneHighFamilyCommonPairs bi bj ↔
      x ∈ oneHighFamilyBlockVertices bi ∧
        z ∈ oneHighFamilyBlockVertices bj := by
  rw [oneHighFamilyCommonPairs_eq_product]
  exact List.pair_mem_product

theorem oneHighFamilyCollectedCommonsMatch_length
    {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    input.1.size = pairs.length := by
  have hvars := congrArg List.length h.vars_eq
  have halign := h.aligned.length_eq
  simpa using hvars.trans (by simpa using halign.symm)

theorem oneHighFamilyCollectedCommonsMatch_value
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input)
    (hs : OneHighFamilySemanticSound R input.2)
    (i : Nat) (hi : i < input.1.size) :
    let p := pairs.get
      ⟨i, by rw [← oneHighFamilyCollectedCommonsMatch_length h]; exact hi⟩
    dimacsLitValue input.2.2 (input.1.getD i 0) =
      oneHighFamilyAtomValue R (.common (min p.1 p.2) (max p.1 p.2)) := by
  have hidsLen : h.ids.length = pairs.length := h.aligned.length_eq.symm
  have hiIds : i < h.ids.length := by
    rw [hidsLen, ← oneHighFamilyCollectedCommonsMatch_length h]
    exact hi
  have hiPairs : i < pairs.length := by
    rw [← oneHighFamilyCollectedCommonsMatch_length h]
    exact hi
  let p := pairs.get ⟨i, hiPairs⟩
  have halign := h.aligned.get hiPairs hiIds
  have hiList : i < input.1.toList.length := by simpa using hi
  have hlistGet : input.1.toList[i] =
      (h.ids.get ⟨i, hiIds⟩ : Int) := by
    have hg := List.get_of_eq h.vars_eq ⟨i, hiList⟩
    rw [List.get_eq_getElem] at hg
    calc
      input.1.toList[i] =
          (List.map (fun id : Nat => Int.ofNat id) h.ids)[i]'(by
            simpa using hiIds) := hg
      _ = (h.ids[i]'hiIds : Int) := List.getElem_map _
      _ = (h.ids.get ⟨i, hiIds⟩ : Int) := by rw [List.get_eq_getElem]
  have harrayGet : input.1.getD i 0 =
      (h.ids.get ⟨i, hiIds⟩ : Int) := by
    rw [show input.1.getD i 0 = input.1[i] by simp [Array.getD, hi]]
    rw [← Array.getElem_toList hi]
    exact hlistGet
  rw [harrayGet]
  have hidPos := (hs.ids.id_bounds _ halign).1
  have hidPosInt : 0 < (h.ids.get ⟨i, hiIds⟩ : Int) := by
    exact_mod_cast hidPos
  rw [dimacsLitValue, if_pos hidPosInt]
  exact hs.named _ _ halign

theorem seqPrefixTrue_oneHighFamilyLiteralRow_eq_countP
    (val : DimacsValuation) (vars : Array Int) :
    seqPrefixTrue (oneHighFamilyLiteralRow val vars) vars.size =
      (List.ofFn (oneHighFamilyLiteralRow val vars)).count true := by
  rw [seqPrefixTrue_full_eq_filter_card]
  let v : List.Vector Bool vars.size :=
    ⟨List.ofFn (oneHighFamilyLiteralRow val vars), by simp⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  convert h using 1 <;> simp [v, List.Vector.get]

theorem oneHighFamilyCollectedCommons_values
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (hm : OneHighFamilyCollectedCommonsMatch pairs input)
    (hs : OneHighFamilySemanticSound R input.2) :
    List.ofFn (oneHighFamilyInputAccumRow input) =
      pairs.map (fun p => oneHighFamilyAtomValue R
        (.common (min p.1 p.2) (max p.1 p.2))) := by
  apply List.ext_getElem
  · simp [oneHighFamilyCollectedCommonsMatch_length hm]
  · intro i hiLeft hiRight
    have hi : i < input.1.size := by simpa using hiLeft
    have hv := oneHighFamilyCollectedCommonsMatch_value R hm hs i hi
    simpa [List.getElem_ofFn, oneHighFamilyInputAccumRow,
      oneHighFamilyLiteralRow] using hv

theorem List.count_map_true_eq_filter_toFinset_card
    {α : Type*} [DecidableEq α] (l : List α) (h : l.Nodup)
    (f : α → Bool) :
    (l.map f).count true = (l.toFinset.filter fun x => f x = true).card := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.nodup_cons] at h
      rw [List.map_cons, List.count_cons, ih h.2]
      by_cases hf : f x = true
      · have hxnot : x ∉ (xs.toFinset.filter fun y => f y = true) := by
          simp [h.1]
        rw [List.toFinset_cons, Finset.filter_insert]
        simp [hf, hxnot, Nat.add_comm]
      · have hf' : f x = false := Bool.eq_false_of_not_eq_true hf
        rw [List.toFinset_cons, Finset.filter_insert]
        simp [hf, hf']

theorem oneHighFamilyCommonPair_atomValue
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (hpair : pair < 4) {x z : Nat}
    (hxmem : x ∈ oneHighFamilyBlockVertices (2 * pair))
    (hzmem : z ∈ oneHighFamilyBlockVertices (2 * pair + 1)) :
    oneHighFamilyAtomValue R (.common (min x z) (max x z)) =
      @decide (oneHighFamilyCAtom R (⟨2 * pair, by omega⟩ : Fin 8)
        (⟨x, (oneHighFamilyBlockVertices_mem (by omega) hxmem).1⟩ : Fin 40)
        (⟨z, (oneHighFamilyBlockVertices_mem (by omega) hzmem).1⟩ : Fin 40))
        (Classical.propDecidable _) := by
  have hx := oneHighFamilyBlockVertices_mem (by omega) hxmem
  have hz := oneHighFamilyBlockVertices_mem (by omega) hzmem
  have hxz : x < z := by omega
  have hmin : (⟨min x z, by omega⟩ : Fin 40) = ⟨x, hx.1⟩ := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt hxz)
  have hmax : (⟨max x z, by omega⟩ : Fin 40) = ⟨z, hz.1⟩ := by
    apply Fin.ext
    exact max_eq_right (Nat.le_of_lt hxz)
  simp only [oneHighFamilyAtomValue, dif_pos (by omega : min x z < 40),
    dif_pos (by omega : max x z < 40)]
  rw [hmin, hmax]
  simp only [oneHighFamilyCAtom,
    oneHighEncodedCommonPairBlock, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and]
  have hxBlock : Fin.divNat (m := 8) (n := 5) (⟨x, hx.1⟩ : Fin 40) =
      (⟨2 * pair, by omega⟩ : Fin 8) := by
    apply Fin.ext
    simpa [Fin.divNat] using hx.2
  have hzBlock : Fin.divNat (m := 8) (n := 5) (⟨z, hz.1⟩ : Fin 40) =
      oneHighStandardMate (⟨2 * pair, by omega⟩ : Fin 8) := by
    rw [oneHighStandardMate_even_pair pair hpair]
    apply Fin.ext
    simpa [Fin.divNat] using hz.2
  simp [hxBlock, hzBlock]

theorem oneHighFamilyBlockVertices_mem_iff
    {b x : Nat} (hb : b < 8) :
    x ∈ oneHighFamilyBlockVertices b ↔ x < 40 ∧ x / 5 = b := by
  constructor
  · exact oneHighFamilyBlockVertices_mem hb
  · rintro ⟨hx, hdiv⟩
    simp only [oneHighFamilyBlockVertices, List.mem_map]
    refine ⟨x % 5, List.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
    omega

set_option maxHeartbeats 400000 in
theorem oneHighFamilyCommonPairs_filter_card
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (pair : Nat) (hpair : pair < 4) :
    let pairs := oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)
    (pairs.toFinset.filter fun p => oneHighFamilyAtomValue R
      (.common (min p.1 p.2) (max p.1 p.2)) = true).card =
      (oneHighFamilyCAtoms R (⟨2 * pair, by omega⟩ : Fin 8)).card := by
  classical
  let pairs := oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)
  apply Finset.card_bij (fun p hp =>
    let hpmem : p ∈ pairs := List.mem_toFinset.mp
      (Finset.mem_filter.mp hp).1
    let hb := mem_oneHighFamilyCommonPairs_iff.mp hpmem
    ((⟨p.1, (oneHighFamilyBlockVertices_mem (by omega) hb.1).1⟩ : Fin 40),
      (⟨p.2, (oneHighFamilyBlockVertices_mem (by omega) hb.2).1⟩ : Fin 40)))
  · intro p hp
    have hpmem : p ∈ pairs := List.mem_toFinset.mp
      (Finset.mem_filter.mp hp).1
    have hb := mem_oneHighFamilyCommonPairs_iff.mp hpmem
    have hv := (Finset.mem_filter.mp hp).2
    rw [oneHighFamilyCommonPair_atomValue R pair hpair hb.1 hb.2] at hv
    have hcAtom : oneHighFamilyCAtom R
        (⟨2 * pair, by omega⟩ : Fin 8)
        (⟨p.1, (oneHighFamilyBlockVertices_mem (by omega) hb.1).1⟩ : Fin 40)
        (⟨p.2, (oneHighFamilyBlockVertices_mem (by omega) hb.2).1⟩ : Fin 40) :=
      @of_decide_eq_true _ (Classical.propDecidable _) hv
    exact hcAtom
  · intro p hp q hq heq
    apply Prod.ext
    · exact congrArg (fun r : Fin 40 × Fin 40 => r.1.val) heq
    · exact congrArg (fun r : Fin 40 × Fin 40 => r.2.val) heq
  · intro q hq
    have hq' := hq
    simp only [oneHighFamilyCAtoms, oneHighEncodedCommonPairBlock,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq'
    rcases hq' with ⟨⟨hxBlock, hzBlock⟩, hcommon⟩
    have hxmem : q.1.val ∈ oneHighFamilyBlockVertices (2 * pair) := by
      apply (oneHighFamilyBlockVertices_mem_iff (by omega)).mpr
      refine ⟨q.1.isLt, ?_⟩
      simpa [Fin.divNat] using congrArg Fin.val hxBlock
    have hzmem : q.2.val ∈ oneHighFamilyBlockVertices (2 * pair + 1) := by
      apply (oneHighFamilyBlockVertices_mem_iff (by omega)).mpr
      refine ⟨q.2.isLt, ?_⟩
      rw [oneHighStandardMate_even_pair pair hpair] at hzBlock
      simpa [Fin.divNat] using congrArg Fin.val hzBlock
    refine ⟨(q.1.val, q.2.val), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr
        (mem_oneHighFamilyCommonPairs_iff.mpr ⟨hxmem, hzmem⟩), ?_⟩
      rw [oneHighFamilyCommonPair_atomValue R pair hpair hxmem hzmem]
      exact @decide_eq_true _ (Classical.propDecidable _) hq
    · apply Prod.ext <;> apply Fin.ext <;> rfl

theorem oneHighFamilyCollectCommonsVal_count
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (pair : Nat) (hpair : pair < 4)
    (acc : OneHighFamilyValState)
    (hacc : OneHighFamilySemanticSound R acc) :
    let input := oneHighFamilyCollectCommonsVal R
      (2 * pair) (2 * pair + 1) acc
    seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
      30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
        2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1) := by
  let input := oneHighFamilyCollectCommonsVal R
    (2 * pair) (2 * pair + 1) acc
  let pairs := oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)
  let hm := oneHighFamilyCollectCommonsVal_match R
    (2 * pair) (2 * pair + 1) acc
  have hs := oneHighFamilyCollectCommonsVal_semanticSound
    a R hc pair hpair acc hacc
  have hvalues := oneHighFamilyCollectedCommons_values R hm hs
  calc
    seqPrefixTrue (oneHighFamilyInputAccumRow input) input.1.size =
        (List.ofFn (oneHighFamilyInputAccumRow input)).count true :=
      seqPrefixTrue_oneHighFamilyLiteralRow_eq_countP input.2.2 input.1
    _ = (pairs.map (fun p => oneHighFamilyAtomValue R
          (.common (min p.1 p.2) (max p.1 p.2)))).count true :=
      congrArg (List.count true) hvalues
    _ = (pairs.toFinset.filter fun p => oneHighFamilyAtomValue R
          (.common (min p.1 p.2) (max p.1 p.2)) = true).card :=
      List.count_map_true_eq_filter_toFinset_card pairs
        (oneHighFamilyCommonPairs_nodup _ _) _
    _ = (oneHighFamilyCAtoms R
          (⟨2 * pair, by omega⟩ : Fin 8)).card :=
      oneHighFamilyCommonPairs_filter_card R pair hpair
    _ = 30 - 2 * oneHighFamilyInternalEdges a
          (⟨2 * pair, by omega⟩ : Fin 8) -
          2 * oneHighFamilyInternalEdges a
            (oneHighStandardMate (⟨2 * pair, by omega⟩ : Fin 8)) :=
      oneHighFamily_cAtoms_card_eq_generatorBound hc.relation _
    _ = 30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
          2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1) := by
      rw [oneHighStandardMate_even_pair pair hpair]
      rfl

theorem oneHighFamilyCollectedCommons_inputSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (hm : OneHighFamilyCollectedCommonsMatch pairs input)
    (hs : OneHighFamilySemanticSound R input.2) :
    OneHighFamilyInputAccumSound R input where
  semantic := hs
  nonzero := by
    intro lit hlit
    have hlitList : lit ∈ input.1.toList := by simpa using hlit
    rw [hm.vars_eq] at hlitList
    rcases List.mem_map.mp hlitList with ⟨id, hid, rfl⟩
    rcases listForall₂_exists_left_of_mem hm.aligned hid with
      ⟨p, _, hatom⟩
    have hpos := (hs.ids.id_bounds _ hatom).1
    exact_mod_cast (Nat.ne_of_gt hpos)
  bounded := by
    intro lit hlit
    have hlitList : lit ∈ input.1.toList := by simpa using hlit
    rw [hm.vars_eq] at hlitList
    rcases List.mem_map.mp hlitList with ⟨id, hid, rfl⟩
    rcases listForall₂_exists_left_of_mem hm.aligned hid with
      ⟨p, _, hatom⟩
    simpa using (hs.ids.id_bounds _ hatom).2

noncomputable def oneHighFamilyPairedProductBlockStepVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a pair : Nat) (acc : OneHighFamilyValState) : OneHighFamilyValState :=
  let bi := 2 * pair
  let bj := bi + 1
  let input := oneHighFamilyCollectCommonsVal R bi bj acc
  let bound := 30 - 2 * oneHighFamilyInternalEdgesNat a bi -
    2 * oneHighFamilyInternalEdgesNat a bj
  oneHighFamilyEqualsBlockVal input.1 (oneHighFamilyInputAccumRow input)
    bound input.2

theorem oneHighFamilyPairedProductBlockStepVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {pair : Nat} (hpair : pair < 4)
    {acc : OneHighFamilyValState}
    (hacc : OneHighFamilySemanticSound R acc) :
    OneHighFamilySemanticSound R
      (oneHighFamilyPairedProductBlockStepVal R a pair acc) := by
  let input := oneHighFamilyCollectCommonsVal R
    (2 * pair) (2 * pair + 1) acc
  have hs := oneHighFamilyCollectCommonsVal_semanticSound
    a R hc pair hpair acc hacc
  let hm := oneHighFamilyCollectCommonsVal_match R
    (2 * pair) (2 * pair + 1) acc
  unfold oneHighFamilyPairedProductBlockStepVal
  apply oneHighFamilyEqualsBlockVal_semanticSound R hs
  · exact oneHighFamilyInputAccum_reifies R
      (oneHighFamilyCollectedCommons_inputSound R hm hs)
  · exact oneHighFamilyCollectCommonsVal_count a R hc pair hpair acc hacc

theorem oneHighFamilyPairedProductBlockStepVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a pair : Nat) (acc : OneHighFamilyValState) :
    (oneHighFamilyPairedProductBlockStepVal R a pair acc).1 =
      oneHighFamilyPairedProductBlockStep a pair acc.1 := by
  have hp := oneHighFamilyCollectCommonsVal_projection R
    (2 * pair) (2 * pair + 1) acc
  simp only [oneHighFamilyPairedProductBlockStepVal,
    oneHighFamilyPairedProductBlockStep]
  generalize hv : oneHighFamilyCollectCommonsVal R
    (2 * pair) (2 * pair + 1) acc = input
  rcases input with ⟨vars, st, val⟩
  rw [hv] at hp
  generalize hg : (oneHighFamilyBlockVertices (2 * pair)).foldl
    (fun input x => (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun input z => oneHighFamilyCommonTseitinStep
        (2 * pair) (2 * pair + 1) x z input) input) (#[], acc.1) = raw
  rcases raw with ⟨rawVars, rawSt⟩
  rw [hg] at hp
  rcases hp with ⟨rfl, rfl⟩
  simp

noncomputable def oneHighFamilyPureClausesVal
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) : OneHighFamilyValState :=
  oneHighFamilyRunListVal (List.range 4)
    (oneHighFamilyPairedProductBlockStepVal R a)
    (oneHighFamilyLexClausesVal R a val)

theorem oneHighFamilyPureClausesVal_semanticSound
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (val : DimacsValuation) :
    OneHighFamilySemanticSound R (oneHighFamilyPureClausesVal R a val) := by
  apply oneHighFamilyRunListVal_semanticSound_mem R _ _
    (oneHighFamilyLexClausesVal_semanticSound a R hc val)
  intro pair hpair acc hacc
  exact oneHighFamilyPairedProductBlockStepVal_semanticSound a R hc
    (List.mem_range.mp hpair) hacc

theorem oneHighFamilyPureClausesVal_state
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a : Nat) (val : DimacsValuation) :
    (oneHighFamilyPureClausesVal R a val).1 = oneHighFamilyPureClauses a := by
  unfold oneHighFamilyPureClausesVal oneHighFamilyPureClauses
  calc
    _ = oneHighFamilyRunList (List.range 4)
        (oneHighFamilyPairedProductBlockStep a)
        (oneHighFamilyLexClausesVal R a val).1 :=
      oneHighFamilyRunListVal_state _ _ _ _
        (fun pair acc => oneHighFamilyPairedProductBlockStepVal_state R a pair acc)
    _ = _ := by rw [oneHighFamilyLexClausesVal_state]

/-- The complete graph-to-DIMACS composition theorem for a PURE one-high
family.  Counter auxiliaries are existentially supplied by the certified
semantic runner. -/
theorem oneHighFamilyPureClauses_dimacsSatisfiable
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val (oneHighFamilyPureClauses a).clauses := by
  let initial : DimacsValuation := fun _ => false
  let out := oneHighFamilyPureClausesVal R a initial
  have hs := oneHighFamilyPureClausesVal_semanticSound a R hc initial
  have hstate := oneHighFamilyPureClausesVal_state R a initial
  refine ⟨out.2, ?_⟩
  rw [← hstate]
  exact hs.satisfied

def OneHighPureFamilyDimacsUnsat (a : Nat) : Prop :=
  ∀ val : DimacsValuation,
    ¬dimacsFormulaSatisfied val (oneHighFamilyPureClauses a).clauses

theorem oneHighPureFamily_constraints_false_of_dimacsUnsat
    {a : Nat} (hunsat : OneHighPureFamilyDimacsUnsat a) :
    ∀ (R : SimpleGraph (Fin 40)) (_ : DecidableRel R.Adj),
      OneHighPureFamilyCnfConstraints a R → False := by
  intro R _ hc
  rcases oneHighFamilyPureClauses_dimacsSatisfiable a R hc with ⟨val, hval⟩
  exact hunsat val hval

def oneHighFamilyPureSatCnf (a : Nat) : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses (oneHighFamilyPureClauses a).clauses

theorem oneHighFamilyPureSatCnf_sat_of_constraints
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (hnz : ∀ clause ∈ (oneHighFamilyPureClauses a).clauses,
      DimacsClauseNonzero clause) :
    ∃ assignment : Nat → Bool,
      (oneHighFamilyPureSatCnf a).Sat assignment := by
  rcases oneHighFamilyPureClauses_dimacsSatisfiable a R hc with ⟨val, hval⟩
  exact ⟨satAssignmentOfDimacs val,
    satCnf_of_dimacsFormulaSatisfied hnz hval⟩

end Erdos85
