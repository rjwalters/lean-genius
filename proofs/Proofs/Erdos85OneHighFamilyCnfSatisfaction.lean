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
      (b := 0) (by omega) (by native_decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 2) (by omega) (by native_decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 4) (by omega) (by native_decide)
  · exact oneHighFamilyMateBlockStepVal_semanticSound a R hc hacc
      (b := 6) (by omega) (by native_decide)

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

theorem oneHighStandardMate_val_eq_xor (b : Fin 8) :
    (oneHighStandardMate b).val = b.val ^^^ 1 := by
  native_decide +revert

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
  vars_eq : input.1.toList = ids.map (fun id => (id : Int))
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
