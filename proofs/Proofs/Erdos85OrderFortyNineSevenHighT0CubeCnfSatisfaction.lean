import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf
import Proofs.Erdos85OrderFortyNineDimacsRows
import Proofs.Erdos85SequentialCounterReification

/-!
# Semantic valuation infrastructure for the seven-high `t = 0` cubes

This file begins the constructive half of the cube bridge.  It proves that
the exact named `IDPool` used by the cube generator remains injective and
bounded, and installs the graph meaning of every named edge/common atom.
Sequential-counter witnesses can then be layered above this named valuation.
-/

namespace Erdos85

structure SevenHighT0CubeIdsSound (st : SevenHighT0CubeGenState) : Prop where
  keys_nodup : (st.ids.map Prod.fst).Nodup
  ids_nodup : (st.ids.map Prod.snd).Nodup
  id_bounds : ∀ entry ∈ st.ids, 0 < entry.2 ∧ entry.2 ≤ st.top

theorem sevenHighT0CubeLookup_eq_none_iff
    (atom : SevenHighT0CubeAtom)
    (ids : List (SevenHighT0CubeAtom × Nat)) :
    sevenHighT0CubeLookup atom ids = none ↔ atom ∉ ids.map Prod.fst := by
  induction ids with
  | nil => simp [sevenHighT0CubeLookup]
  | cons entry rest ih =>
      simp only [sevenHighT0CubeLookup, List.map_cons, List.mem_cons]
      by_cases heq : entry.1 = atom
      · rw [if_pos heq]
        constructor
        · intro h
          contradiction
        · intro h
          exact False.elim (h (Or.inl heq.symm))
      · rw [if_neg heq, ih]
        constructor
        · intro h hor
          rcases hor with ha | ha
          · exact heq ha.symm
          · exact h ha
        · intro h ha
          exact h (Or.inr ha)

theorem sevenHighT0CubeLookup_eq_some_mem
    {atom : SevenHighT0CubeAtom} {id : Nat}
    {ids : List (SevenHighT0CubeAtom × Nat)}
    (h : sevenHighT0CubeLookup atom ids = some id) :
    (atom, id) ∈ ids := by
  induction ids with
  | nil => simp [sevenHighT0CubeLookup] at h
  | cons entry rest ih =>
      rw [List.mem_cons]
      rw [sevenHighT0CubeLookup] at h
      split at h
      next heq =>
        simp only [Option.some.injEq] at h
        subst id
        exact Or.inl (Prod.ext heq.symm rfl)
      next => exact Or.inr (ih h)

theorem sevenHighT0CubeIdsSound_initial :
    SevenHighT0CubeIdsSound ({} : SevenHighT0CubeGenState) := by
  constructor <;> simp

theorem sevenHighT0CubeIdsSound_atomId
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (atom : SevenHighT0CubeAtom) :
    SevenHighT0CubeIdsSound (sevenHighT0CubeAtomId atom st).2 := by
  unfold sevenHighT0CubeAtomId
  split
  next id hlookup => simpa using h
  next hlookup =>
    constructor
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨(sevenHighT0CubeLookup_eq_none_iff atom st.ids).mp hlookup,
        h.keys_nodup⟩
    · simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
        have hb := (h.id_bounds entry hentry).2
        omega
      · exact h.ids_nodup
    · intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp
      · have hb := h.id_bounds entry hentry
        exact ⟨hb.1, hb.2.trans (Nat.le_succ _)⟩

theorem sevenHighT0CubeAtomId_mem (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) :
    (atom, (sevenHighT0CubeAtomId atom st).1) ∈
      (sevenHighT0CubeAtomId atom st).2.ids := by
  unfold sevenHighT0CubeAtomId
  split
  next id hlookup => exact sevenHighT0CubeLookup_eq_some_mem hlookup
  next => simp

theorem sevenHighT0CubeAtomId_ids_subset (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) :
    ∀ entry ∈ st.ids, entry ∈ (sevenHighT0CubeAtomId atom st).2.ids := by
  unfold sevenHighT0CubeAtomId
  split
  · exact fun _ hentry => hentry
  · intro entry hentry
    exact List.mem_cons_of_mem _ hentry

theorem sevenHighT0CubeIdsSound_edgeId
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (i j : Nat) :
    SevenHighT0CubeIdsSound (sevenHighT0CubeEdgeId i j st).2 := by
  exact sevenHighT0CubeIdsSound_atomId h _

theorem sevenHighT0CubeIdsSound_commonId
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (i j w : Nat) :
    SevenHighT0CubeIdsSound (sevenHighT0CubeCommonId i j w st).2 := by
  exact sevenHighT0CubeIdsSound_atomId h _

theorem sevenHighT0CubeIdsSound_emit
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (clause : DimacsClause) :
    SevenHighT0CubeIdsSound (sevenHighT0CubeEmit clause st) := by
  exact { h with }

def sevenHighT0CubeLookupId (id : Nat) :
    List (SevenHighT0CubeAtom × Nat) → Option SevenHighT0CubeAtom
  | [] => none
  | entry :: rest =>
      if entry.2 = id then some entry.1 else sevenHighT0CubeLookupId id rest

theorem sevenHighT0CubeLookupId_of_mem
    {atom : SevenHighT0CubeAtom} {id : Nat}
    {ids : List (SevenHighT0CubeAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    sevenHighT0CubeLookupId id ids = some atom := by
  induction ids with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hidFresh, hrest⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [sevenHighT0CubeLookupId]
      · have hne : entry.2 ≠ id := by
          intro heq
          apply hidFresh
          exact List.mem_map.mpr ⟨(atom, id), hmem, by simpa [heq]⟩
        simp [sevenHighT0CubeLookupId, hne, ih hrest hmem]

def sevenHighT0CubeAtomValue (adj : Fin 49 → Fin 49 → Bool) :
    SevenHighT0CubeAtom → Bool
  | .edge i j =>
      if hi : i < 49 then if hj : j < 49 then adj ⟨i, hi⟩ ⟨j, hj⟩
      else false else false
  | .common i j w =>
      if hi : i < 49 then if hj : j < 49 then if hw : w < 49 then
        adj ⟨i, hi⟩ ⟨w, hw⟩ && adj ⟨j, hj⟩ ⟨w, hw⟩
      else false else false else false

def sevenHighT0CubeNamedVal (adj : Fin 49 → Fin 49 → Bool)
    (ids : List (SevenHighT0CubeAtom × Nat)) : DimacsValuation := fun id =>
  match sevenHighT0CubeLookupId id ids with
  | some atom => sevenHighT0CubeAtomValue adj atom
  | none => false

theorem sevenHighT0CubeNamedVal_of_mem
    (adj : Fin 49 → Fin 49 → Bool)
    {atom : SevenHighT0CubeAtom} {id : Nat}
    {ids : List (SevenHighT0CubeAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    sevenHighT0CubeNamedVal adj ids id =
      sevenHighT0CubeAtomValue adj atom := by
  rw [sevenHighT0CubeNamedVal,
    sevenHighT0CubeLookupId_of_mem hnodup hmem]

def SevenHighT0CubeNamedValReifies
    (adj : Fin 49 → Fin 49 → Bool)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation) : Prop :=
  ∀ atom id, (atom, id) ∈ st.ids →
    val id = sevenHighT0CubeAtomValue adj atom

theorem sevenHighT0CubeNamedVal_reifies
    (adj : Fin 49 → Fin 49 → Bool) (st : SevenHighT0CubeGenState)
    (h : SevenHighT0CubeIdsSound st) :
    SevenHighT0CubeNamedValReifies adj st
      (sevenHighT0CubeNamedVal adj st.ids) := by
  intro atom id hmem
  exact sevenHighT0CubeNamedVal_of_mem adj h.ids_nodup hmem

abbrev SevenHighT0CubeValState :=
  SevenHighT0CubeGenState × DimacsValuation

/-- Allocate one named atom exactly as the generator does and install its
graph-semantic value at the returned identifier. -/
def sevenHighT0CubeAtomIdVal
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (acc : SevenHighT0CubeValState) : Nat × SevenHighT0CubeValState :=
  let (st, val) := acc
  let (id, st') := sevenHighT0CubeAtomId atom st
  (id, (st', Function.update val id (sevenHighT0CubeAtomValue adj atom)))

def sevenHighT0CubeEdgeIdVal
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState) : Nat × SevenHighT0CubeValState :=
  sevenHighT0CubeAtomIdVal adj (.edge (min i j) (max i j)) acc

def sevenHighT0CubeCommonIdVal
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    (acc : SevenHighT0CubeValState) : Nat × SevenHighT0CubeValState :=
  sevenHighT0CubeAtomIdVal adj (.common i j w) acc

@[simp] theorem sevenHighT0CubeAtomIdVal_state
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation) :
    (sevenHighT0CubeAtomIdVal adj atom (st, val)).2.1 =
      (sevenHighT0CubeAtomId atom st).2 := by
  generalize h : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [sevenHighT0CubeAtomIdVal, h]

@[simp] theorem sevenHighT0CubeAtomIdVal_id
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation) :
    (sevenHighT0CubeAtomIdVal adj atom (st, val)).1 =
      (sevenHighT0CubeAtomId atom st).1 := by
  generalize h : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [sevenHighT0CubeAtomIdVal, h]

@[simp] theorem sevenHighT0CubeAtomIdVal_value
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation) :
    (sevenHighT0CubeAtomIdVal adj atom (st, val)).2.2
        (sevenHighT0CubeAtomId atom st).1 =
      sevenHighT0CubeAtomValue adj atom := by
  generalize h : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simp [sevenHighT0CubeAtomIdVal, h]

theorem sevenHighT0CubeAtomIdVal_result
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation) :
    let out := sevenHighT0CubeAtomIdVal adj atom (st, val)
    (atom, out.1) ∈ out.2.1.ids ∧
      out.2.2 out.1 = sevenHighT0CubeAtomValue adj atom := by
  generalize h : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  constructor
  · simpa [sevenHighT0CubeAtomIdVal, h] using
      sevenHighT0CubeAtomId_mem atom st
  · simp [sevenHighT0CubeAtomIdVal, h]

theorem sevenHighT0CubeAtomIdVal_old_mem
    (adj : Fin 49 → Fin 49 → Bool) (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) (val : DimacsValuation)
    {entry : SevenHighT0CubeAtom × Nat} (hmem : entry ∈ st.ids) :
    let out := sevenHighT0CubeAtomIdVal adj atom (st, val)
    entry ∈ out.2.1.ids := by
  generalize h : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  simpa [sevenHighT0CubeAtomIdVal, h] using
    sevenHighT0CubeAtomId_ids_subset atom st entry hmem

theorem sevenHighT0CubeAtomIdVal_reifies
    (adj : Fin 49 → Fin 49 → Bool)
    {st : SevenHighT0CubeGenState} {val : DimacsValuation}
    (hsound : SevenHighT0CubeIdsSound st)
    (hreifies : SevenHighT0CubeNamedValReifies adj st val)
    (atom : SevenHighT0CubeAtom) :
    let out := sevenHighT0CubeAtomIdVal adj atom (st, val)
    SevenHighT0CubeNamedValReifies adj out.2.1 out.2.2 := by
  simp only [sevenHighT0CubeAtomIdVal]
  generalize hout : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  unfold sevenHighT0CubeAtomId at hout
  split at hout
  next _ hlookup =>
    cases hout
    intro atom' id' hmem
    have hatomMem : (atom, id) ∈ st.ids :=
      sevenHighT0CubeLookup_eq_some_mem hlookup
    have hlookupAtom := sevenHighT0CubeLookupId_of_mem
      hsound.ids_nodup hatomMem
    have hlookupAtom' := sevenHighT0CubeLookupId_of_mem
      hsound.ids_nodup hmem
    by_cases hid : id' = id
    · subst id'
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

def sevenHighT0CubeEmitVal (clause : DimacsClause)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  (sevenHighT0CubeEmit clause acc.1, acc.2)

structure SevenHighT0CubeSemanticSound
    (adj : Fin 49 → Fin 49 → Bool)
    (acc : SevenHighT0CubeValState) : Prop where
  ids : SevenHighT0CubeIdsSound acc.1
  named : SevenHighT0CubeNamedValReifies adj acc.1 acc.2
  satisfied : dimacsFormulaSatisfied acc.2 acc.1.clauses
  bounded : dimacsFormulaBounded acc.1.top acc.1.clauses

theorem sevenHighT0CubeSemanticSound_initial
    (adj : Fin 49 → Fin 49 → Bool) (val : DimacsValuation) :
    SevenHighT0CubeSemanticSound adj
      (({} : SevenHighT0CubeGenState), val) where
  ids := sevenHighT0CubeIdsSound_initial
  named := by intro atom id hmem; simp at hmem
  satisfied := dimacsFormulaSatisfied_empty val
  bounded := dimacsFormulaBounded_empty 0

theorem sevenHighT0CubeAtomIdVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool)
    {st : SevenHighT0CubeGenState} {val : DimacsValuation}
    (h : SevenHighT0CubeSemanticSound adj (st, val))
    (atom : SevenHighT0CubeAtom) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeAtomIdVal adj atom (st, val)).2 := by
  simp only [sevenHighT0CubeAtomIdVal]
  generalize hout : sevenHighT0CubeAtomId atom st = out
  rcases out with ⟨id, st'⟩
  unfold sevenHighT0CubeAtomId at hout
  split at hout
  next _ hlookup =>
    cases hout
    have hmem : (atom, id) ∈ st.ids :=
      sevenHighT0CubeLookup_eq_some_mem hlookup
    have hvalue : val id = sevenHighT0CubeAtomValue adj atom :=
      h.named atom id hmem
    have hvalEq : Function.update val id
        (sevenHighT0CubeAtomValue adj atom) = val := by
      funext k
      by_cases hk : k = id
      · subst k
        simp [hvalue]
      · simp [Function.update, hk]
    simpa [hvalEq] using h
  next hlookup =>
    cases hout
    let nextVal := Function.update val (st.top + 1)
      (sevenHighT0CubeAtomValue adj atom)
    have hagree : ∀ id, id ≤ st.top → val id = nextVal id := by
      intro id hid
      have hne : id ≠ st.top + 1 := by omega
      simp [nextVal, hne]
    have hsat : dimacsFormulaSatisfied nextVal st.clauses :=
      dimacsFormulaSatisfied_of_bounded_agree h.satisfied h.bounded hagree
    constructor
    · simpa [sevenHighT0CubeAtomId, hlookup] using
        sevenHighT0CubeIdsSound_atomId h.ids atom
    · simpa [sevenHighT0CubeAtomIdVal, sevenHighT0CubeAtomId, hlookup] using
        sevenHighT0CubeAtomIdVal_reifies adj h.ids h.named atom
    · exact hsat
    · exact dimacsFormulaBounded_mono (Nat.le_succ st.top) h.bounded

theorem sevenHighT0CubeEmitVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool)
    {st : SevenHighT0CubeGenState} {val : DimacsValuation}
    (h : SevenHighT0CubeSemanticSound adj (st, val))
    (clause : DimacsClause)
    (hclauseSat : dimacsClauseSatisfied val clause)
    (hclauseBound : dimacsClauseBounded st.top clause) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeEmitVal clause (st, val)) := by
  constructor
  · exact sevenHighT0CubeIdsSound_emit h.ids clause
  · exact h.named
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

/-- Semantic wrapper for the exact PySAT equality block used by each degree
constraint.  Named IDs are unchanged; only the fresh counter interval and its
canonical valuation are added. -/
def sevenHighT0CubeEqualsBlock (vars : Array Int) (bound : Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let out := seqCounterEquals st.top vars bound
  { st with top := out.top, clauses := st.clauses ++ out.clauses }

def sevenHighT0CubeEqualsBlockVal (vars : Array Int)
    (x : Fin vars.size → Bool) (bound : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  (sevenHighT0CubeEqualsBlock vars bound acc.1,
    seqCounterEqualsVal acc.2 acc.1.top vars x bound)

@[simp] theorem sevenHighT0CubeEqualsBlockVal_state
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeEqualsBlockVal vars x bound acc).1 =
      sevenHighT0CubeEqualsBlock vars bound acc.1 := by
  rfl

theorem sevenHighT0CubeIdsSound_equalsBlock
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (vars : Array Int) (bound : Nat) :
    SevenHighT0CubeIdsSound
      (sevenHighT0CubeEqualsBlock vars bound st) := by
  constructor
  · exact h.keys_nodup
  · exact h.ids_nodup
  · intro entry hentry
    have hb := h.id_bounds entry hentry
    exact ⟨hb.1, hb.2.trans (by
      simpa [sevenHighT0CubeEqualsBlock] using
        seqCounterEquals_top_bound st.top vars bound)⟩

theorem sevenHighT0CubeEqualsBlockVal_reifies
    (adj : Fin 49 → Fin 49 → Bool)
    {st : SevenHighT0CubeGenState} {val : DimacsValuation}
    (hsound : SevenHighT0CubeIdsSound st)
    (hreifies : SevenHighT0CubeNamedValReifies adj st val)
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat) :
    SevenHighT0CubeNamedValReifies adj
      (sevenHighT0CubeEqualsBlockVal vars x bound (st, val)).1
      (sevenHighT0CubeEqualsBlockVal vars x bound (st, val)).2 := by
  intro atom id hmem
  have hid := (hsound.id_bounds (atom, id) hmem).2
  exact (seqCounterEqualsVal_input val st.top vars x bound id hid).trans
    (hreifies atom id hmem)

theorem sevenHighT0CubeEqualsBlockVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool)
    {st : SevenHighT0CubeGenState} {val : DimacsValuation}
    (h : SevenHighT0CubeSemanticSound adj (st, val))
    (vars : Array Int) (x : Fin vars.size → Bool) (bound : Nat)
    (hinput : SeqCounterInputReifies val st.top vars x)
    (hcount : seqPrefixTrue x vars.size = bound) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeEqualsBlockVal vars x bound (st, val)) := by
  let hblock := seqCounterEqualsVal_formulaSatisfied_append
    val st.top st.clauses vars x h.satisfied h.bounded hinput bound hcount
  constructor
  · exact sevenHighT0CubeIdsSound_equalsBlock h.ids vars bound
  · exact sevenHighT0CubeEqualsBlockVal_reifies adj h.ids h.named
      vars x bound
  · simpa [sevenHighT0CubeEqualsBlockVal,
      sevenHighT0CubeEqualsBlock] using hblock.1
  · simpa [sevenHighT0CubeEqualsBlockVal,
      sevenHighT0CubeEqualsBlock] using hblock.2.1

theorem sevenHighT0CubeSemanticSound_foldl
    {α : Type} (adj : Fin 49 → Fin 49 → Bool) (xs : List α)
    (step : α → SevenHighT0CubeValState → SevenHighT0CubeValState)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hstep : ∀ x acc, SevenHighT0CubeSemanticSound adj acc →
      SevenHighT0CubeSemanticSound adj (step x acc)) :
    SevenHighT0CubeSemanticSound adj (xs.foldl (fun acc x => step x acc) acc) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (hstep x acc hacc)

theorem sevenHighT0CubeSemanticSound_foldl_mem
    {α : Type} (adj : Fin 49 → Fin 49 → Bool) (xs : List α)
    (step : α → SevenHighT0CubeValState → SevenHighT0CubeValState)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hstep : ∀ x, x ∈ xs → ∀ acc,
      SevenHighT0CubeSemanticSound adj acc →
      SevenHighT0CubeSemanticSound adj (step x acc)) :
    SevenHighT0CubeSemanticSound adj (xs.foldl (fun acc x => step x acc) acc) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (hstep x (by simp) acc hacc)
      intro y hy acc hacc
      exact hstep y (by simp [hy]) acc hacc

theorem sevenHighT0CubeAtomId_positive
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (atom : SevenHighT0CubeAtom) :
    0 < (sevenHighT0CubeAtomId atom st).1 := by
  let out := sevenHighT0CubeAtomId atom st
  have hs := sevenHighT0CubeIdsSound_atomId h atom
  have hm := sevenHighT0CubeAtomId_mem atom st
  exact (hs.id_bounds (atom, out.1) (by simpa [out] using hm)).1

theorem sevenHighT0CubeAtomId_bounded
    {st : SevenHighT0CubeGenState} (h : SevenHighT0CubeIdsSound st)
    (atom : SevenHighT0CubeAtom) :
    (sevenHighT0CubeAtomId atom st).1 ≤
      (sevenHighT0CubeAtomId atom st).2.top := by
  let out := sevenHighT0CubeAtomId atom st
  have hs := sevenHighT0CubeIdsSound_atomId h atom
  have hm := sevenHighT0CubeAtomId_mem atom st
  exact (hs.id_bounds (atom, out.1) (by simpa [out] using hm)).2

theorem sevenHighT0CubeSingleton_positive_satisfied
    {val : DimacsValuation} {id : Nat} (hid : 0 < id)
    (hvalue : val id = true) :
    dimacsClauseSatisfied val [(id : Int)] := by
  refine ⟨(id : Int), by simp, ?_⟩
  simp [dimacsLitValue, hid, hvalue]

theorem sevenHighT0CubeSingleton_negative_satisfied
    {val : DimacsValuation} {id : Nat} (hvalue : val id = false) :
    dimacsClauseSatisfied val [-(id : Int)] := by
  refine ⟨-(id : Int), by simp, ?_⟩
  simp [dimacsLitValue, hvalue]

theorem sevenHighT0CubeSingleton_positive_bounded
    {top id : Nat} (hid : id ≤ top) :
    dimacsClauseBounded top [(id : Int)] := by
  intro lit hlit
  simp at hlit
  simpa [hlit] using hid

theorem sevenHighT0CubeSingleton_negative_bounded
    {top id : Nat} (hid : id ≤ top) :
    dimacsClauseBounded top [-(id : Int)] := by
  intro lit hlit
  simp at hlit
  simpa [hlit] using hid

def sevenHighT0CubeEmitEdgeUnitVal
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat) (positive : Bool)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let (id, acc) := sevenHighT0CubeEdgeIdVal adj i j acc
  sevenHighT0CubeEmitVal
    [if positive then (id : Int) else -(id : Int)] acc

theorem sevenHighT0CubeEmitEdgeUnitVal_state
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat) (positive : Bool)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeEmitEdgeUnitVal adj i j positive acc).1 =
      sevenHighT0CubeEmitEdgeUnit i j positive acc.1 := by
  generalize h : sevenHighT0CubeEdgeId i j acc.1 = out
  rcases out with ⟨id, st'⟩
  simp [sevenHighT0CubeEmitEdgeUnitVal, sevenHighT0CubeEdgeIdVal,
    sevenHighT0CubeEdgeId, sevenHighT0CubeAtomIdVal, h,
    sevenHighT0CubeEmitVal, sevenHighT0CubeEmitEdgeUnit]

theorem sevenHighT0CubeEmitEdgeUnitVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat) (positive : Bool)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hvalue : sevenHighT0CubeAtomValue adj
      (.edge (min i j) (max i j)) = positive) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeEmitEdgeUnitVal adj i j positive acc) := by
  generalize hallocated : sevenHighT0CubeEdgeIdVal adj i j acc = allocated
  rcases allocated with ⟨id, st', val'⟩
  have hallocatedAtom : sevenHighT0CubeAtomIdVal adj
      (.edge (min i j) (max i j)) (acc.1, acc.2) = (id, st', val') := by
    simpa [sevenHighT0CubeEdgeIdVal] using hallocated
  have ha : SevenHighT0CubeSemanticSound adj (st', val') := by
    have ha' := sevenHighT0CubeAtomIdVal_semanticSound adj hacc
      (.edge (min i j) (max i j))
    rw [hallocatedAtom] at ha'
    exact ha'
  have hresult := sevenHighT0CubeAtomIdVal_result adj
    (.edge (min i j) (max i j)) acc.1 acc.2
  have hv : val' id = positive := by
    calc
      val' id =
          sevenHighT0CubeAtomValue adj
            (.edge (min i j) (max i j)) := by
              rw [hallocatedAtom] at hresult
              exact hresult.2
      _ = positive := hvalue
  have hm :
      (.edge (min i j) (max i j), id) ∈ st'.ids := by
    rw [hallocatedAtom] at hresult
    exact hresult.1
  have hidpos : 0 < id := (ha.ids.id_bounds _ hm).1
  have hidbound : id ≤ st'.top := (ha.ids.id_bounds _ hm).2
  unfold sevenHighT0CubeEmitEdgeUnitVal
  rw [hallocated]
  apply sevenHighT0CubeEmitVal_semanticSound adj ha
  · cases hp : positive
    · rw [hp] at hv
      exact sevenHighT0CubeSingleton_negative_satisfied hv
    · rw [hp] at hv
      exact sevenHighT0CubeSingleton_positive_satisfied hidpos hv
  · cases hp : positive
    · simpa [hp] using
        sevenHighT0CubeSingleton_negative_bounded hidbound
    · simpa [hp] using
        sevenHighT0CubeSingleton_positive_bounded hidbound

theorem sevenHighT0CubeFoldl_state
    {α : Type} (xs : List α)
    (stepVal : α → SevenHighT0CubeValState → SevenHighT0CubeValState)
    (step : α → SevenHighT0CubeGenState → SevenHighT0CubeGenState)
    (acc : SevenHighT0CubeValState)
    (hstep : ∀ x acc, (stepVal x acc).1 = step x acc.1) :
    (xs.foldl (fun acc x => stepVal x acc) acc).1 =
      xs.foldl (fun st x => step x st) acc.1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        _ = xs.foldl (fun st x => step x st) (stepVal x acc).1 :=
          ih (stepVal x acc)
        _ = _ := by rw [hstep x acc]

def sevenHighT0CubeHighIndependentVal
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    SevenHighT0CubeValState :=
  (sevenHighT0CubePairs sevenHighT0CubeHighs).foldl (fun acc pair =>
    sevenHighT0CubeEmitEdgeUnitVal adj pair.1 pair.2 false acc)
    (({} : SevenHighT0CubeGenState), initial)

theorem sevenHighT0CubeHighIndependentVal_state
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    (sevenHighT0CubeHighIndependentVal adj initial).1 =
      sevenHighT0CubeHighIndependent := by
  unfold sevenHighT0CubeHighIndependentVal sevenHighT0CubeHighIndependent
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun pair acc =>
      sevenHighT0CubeEmitEdgeUnitVal_state adj pair.1 pair.2 false acc)

theorem sevenHighT0CubeHighIndependentVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation)
    (hindependent : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 pair.2) (max pair.1 pair.2)) = false) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeHighIndependentVal adj initial) := by
  unfold sevenHighT0CubeHighIndependentVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _
    (sevenHighT0CubeSemanticSound_initial adj initial)
  intro pair hpair acc hacc
  apply sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj
    pair.1 pair.2 false hacc
  exact hindependent pair hpair

def sevenHighT0CubeNormalizeN0Val
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    SevenHighT0CubeValState :=
  let acc := sevenHighT0CubeLows.foldl (fun acc x =>
    sevenHighT0CubeEmitEdgeUnitVal adj 0 x (x < 15) acc)
    (sevenHighT0CubeHighIndependentVal adj initial)
  (sevenHighT0CubePairs sevenHighT0CubeN0).foldl (fun acc pair =>
    sevenHighT0CubeEmitEdgeUnitVal adj pair.1 pair.2
      (sevenHighT0CubeMatching0 pair.1 pair.2) acc) acc

theorem sevenHighT0CubeNormalizeN0Val_state
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    (sevenHighT0CubeNormalizeN0Val adj initial).1 =
      sevenHighT0CubeNormalizeN0 := by
  unfold sevenHighT0CubeNormalizeN0Val sevenHighT0CubeNormalizeN0
  let lowVal := sevenHighT0CubeLows.foldl (fun acc x =>
    sevenHighT0CubeEmitEdgeUnitVal adj 0 x (x < 15) acc)
    (sevenHighT0CubeHighIndependentVal adj initial)
  let lowState := sevenHighT0CubeLows.foldl (fun st x =>
    sevenHighT0CubeEmitEdgeUnit 0 x (x < 15) st)
    sevenHighT0CubeHighIndependent
  have hlow : lowVal.1 = lowState := by
    unfold lowVal lowState
    calc
      _ = sevenHighT0CubeLows.foldl (fun st x =>
          sevenHighT0CubeEmitEdgeUnit 0 x (x < 15) st)
          (sevenHighT0CubeHighIndependentVal adj initial).1 :=
        sevenHighT0CubeFoldl_state _ _ _ _
          (fun x acc => sevenHighT0CubeEmitEdgeUnitVal_state adj 0 x
            (x < 15) acc)
      _ = _ := by rw [sevenHighT0CubeHighIndependentVal_state]
  calc
    _ = (sevenHighT0CubePairs sevenHighT0CubeN0).foldl
        (fun st pair => sevenHighT0CubeEmitEdgeUnit pair.1 pair.2
          (sevenHighT0CubeMatching0 pair.1 pair.2) st) lowVal.1 :=
      sevenHighT0CubeFoldl_state _ _ _ _
        (fun pair acc => sevenHighT0CubeEmitEdgeUnitVal_state adj
          pair.1 pair.2 (sevenHighT0CubeMatching0 pair.1 pair.2) acc)
    _ = _ := by rw [hlow]

theorem sevenHighT0CubeNormalizeN0Val_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation)
    (hindependent : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 pair.2) (max pair.1 pair.2)) = false)
    (hn0 : ∀ x ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.edge 0 x) = decide (x < 15))
    (hmatching : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN0,
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 pair.2) (max pair.1 pair.2)) =
        sevenHighT0CubeMatching0 pair.1 pair.2) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeNormalizeN0Val adj initial) := by
  unfold sevenHighT0CubeNormalizeN0Val
  have hhigh := sevenHighT0CubeHighIndependentVal_semanticSound
    adj initial hindependent
  have hlow : SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeLows.foldl (fun acc x =>
        sevenHighT0CubeEmitEdgeUnitVal adj 0 x (x < 15) acc)
        (sevenHighT0CubeHighIndependentVal adj initial)) := by
    apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hhigh
    intro x hx acc hacc
    apply sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj 0 x
      (x < 15) hacc
    simpa using hn0 x hx
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hlow
  intro pair hp acc hacc
  exact sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj pair.1 pair.2
    (sevenHighT0CubeMatching0 pair.1 pair.2) hacc (hmatching pair hp)

def sevenHighT0CubeNormalizeN1Val
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    SevenHighT0CubeValState :=
  let acc := sevenHighT0CubeEmitEdgeUnitVal adj 1 7 true
    (sevenHighT0CubeNormalizeN0Val adj initial)
  let acc := (List.range 7).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 8) false acc) acc
  let acc := (List.range 7).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 15) true acc) acc
  let acc := (List.range 27).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 22) false acc) acc
  (sevenHighT0CubePairs sevenHighT0CubeN1).foldl (fun acc pair =>
    sevenHighT0CubeEmitEdgeUnitVal adj pair.1 pair.2
      (sevenHighT0CubeMatching1 pair.1 pair.2) acc) acc

theorem sevenHighT0CubeNormalizeN1Val_state
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation) :
    (sevenHighT0CubeNormalizeN1Val adj initial).1 =
      sevenHighT0CubeNormalizeN1 := by
  unfold sevenHighT0CubeNormalizeN1Val sevenHighT0CubeNormalizeN1
  let a0 := sevenHighT0CubeEmitEdgeUnitVal adj 1 7 true
    (sevenHighT0CubeNormalizeN0Val adj initial)
  let s0 := sevenHighT0CubeEmitEdgeUnit 1 7 true sevenHighT0CubeNormalizeN0
  have h0 : a0.1 = s0 := by
    unfold a0 s0
    rw [sevenHighT0CubeEmitEdgeUnitVal_state,
      sevenHighT0CubeNormalizeN0Val_state]
  let a1 := (List.range 7).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 8) false acc) a0
  let s1 := (List.range 7).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 8) false st) s0
  have h1 : a1.1 = s1 := by
    unfold a1 s1
    calc
      _ = (List.range 7).foldl (fun st k =>
          sevenHighT0CubeEmitEdgeUnit 1 (k + 8) false st) a0.1 :=
        sevenHighT0CubeFoldl_state _ _ _ _
          (fun k acc => sevenHighT0CubeEmitEdgeUnitVal_state adj 1
            (k + 8) false acc)
      _ = _ := by rw [h0]
  let a2 := (List.range 7).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 15) true acc) a1
  let s2 := (List.range 7).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 15) true st) s1
  have h2 : a2.1 = s2 := by
    unfold a2 s2
    calc
      _ = (List.range 7).foldl (fun st k =>
          sevenHighT0CubeEmitEdgeUnit 1 (k + 15) true st) a1.1 :=
        sevenHighT0CubeFoldl_state _ _ _ _
          (fun k acc => sevenHighT0CubeEmitEdgeUnitVal_state adj 1
            (k + 15) true acc)
      _ = _ := by rw [h1]
  let a3 := (List.range 27).foldl (fun acc k =>
    sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 22) false acc) a2
  let s3 := (List.range 27).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 22) false st) s2
  have h3 : a3.1 = s3 := by
    unfold a3 s3
    calc
      _ = (List.range 27).foldl (fun st k =>
          sevenHighT0CubeEmitEdgeUnit 1 (k + 22) false st) a2.1 :=
        sevenHighT0CubeFoldl_state _ _ _ _
          (fun k acc => sevenHighT0CubeEmitEdgeUnitVal_state adj 1
            (k + 22) false acc)
      _ = _ := by rw [h2]
  calc
    _ = (sevenHighT0CubePairs sevenHighT0CubeN1).foldl
        (fun st pair => sevenHighT0CubeEmitEdgeUnit pair.1 pair.2
          (sevenHighT0CubeMatching1 pair.1 pair.2) st) a3.1 :=
      sevenHighT0CubeFoldl_state _ _ _ _
        (fun pair acc => sevenHighT0CubeEmitEdgeUnitVal_state adj
          pair.1 pair.2 (sevenHighT0CubeMatching1 pair.1 pair.2) acc)
    _ = _ := by rw [h3]

theorem sevenHighT0CubeNormalizeN1Val_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (initial : DimacsValuation)
    (hn0sound : SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeNormalizeN0Val adj initial))
    (h7 : sevenHighT0CubeAtomValue adj (.edge 1 7) = true)
    (h8 : ∀ k ∈ List.range 7,
      sevenHighT0CubeAtomValue adj (.edge 1 (k + 8)) = false)
    (h15 : ∀ k ∈ List.range 7,
      sevenHighT0CubeAtomValue adj (.edge 1 (k + 15)) = true)
    (h22 : ∀ k ∈ List.range 27,
      sevenHighT0CubeAtomValue adj (.edge 1 (k + 22)) = false)
    (hmatching : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN1,
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 pair.2) (max pair.1 pair.2)) =
        sevenHighT0CubeMatching1 pair.1 pair.2) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeNormalizeN1Val adj initial) := by
  unfold sevenHighT0CubeNormalizeN1Val
  have hs0 := sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj
    1 7 true hn0sound h7
  have hs1 : SevenHighT0CubeSemanticSound adj
      ((List.range 7).foldl (fun acc k =>
        sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 8) false acc)
        (sevenHighT0CubeEmitEdgeUnitVal adj 1 7 true
          (sevenHighT0CubeNormalizeN0Val adj initial))) := by
    apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hs0
    intro k hk acc hacc
    exact sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj 1 (k + 8)
      false hacc (h8 k hk)
  have hs2 := sevenHighT0CubeSemanticSound_foldl_mem adj (List.range 7)
    (fun k acc => sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 15) true acc)
    hs1 (fun k hk acc hacc =>
      sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj 1 (k + 15)
        true hacc (h15 k hk))
  have hs3 := sevenHighT0CubeSemanticSound_foldl_mem adj (List.range 27)
    (fun k acc => sevenHighT0CubeEmitEdgeUnitVal adj 1 (k + 22) false acc)
    hs2 (fun k hk acc hacc =>
      sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj 1 (k + 22)
        false hacc (h22 k hk))
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hs3
  intro pair hp acc hacc
  exact sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj pair.1 pair.2
    (sevenHighT0CubeMatching1 pair.1 pair.2) hacc (hmatching pair hp)

def sevenHighT0CubeFinalUnitsVal
    (adj : Fin 49 → Fin 49 → Bool) (cube : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  (List.range 7).foldl (fun acc index =>
    sevenHighT0CubeEmitEdgeUnitVal adj 9 (index + 15)
      (index = cube) acc) acc

theorem sevenHighT0CubeFinalUnitsVal_state
    (adj : Fin 49 → Fin 49 → Bool) (cube : Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeFinalUnitsVal adj cube acc).1 =
      (List.range 7).foldl (fun st index =>
        sevenHighT0CubeEmitEdgeUnit 9 (index + 15)
          (index = cube) st) acc.1 := by
  unfold sevenHighT0CubeFinalUnitsVal
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun index acc => sevenHighT0CubeEmitEdgeUnitVal_state adj
      9 (index + 15) (index = cube) acc)

theorem sevenHighT0CubeFinalUnitsVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (cube : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hcube : ∀ index ∈ List.range 7,
      sevenHighT0CubeAtomValue adj (.edge 9 (index + 15)) =
        decide (index = cube)) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeFinalUnitsVal adj cube acc) := by
  unfold sevenHighT0CubeFinalUnitsVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro index hi acc hacc
  apply sevenHighT0CubeEmitEdgeUnitVal_semanticSound adj
    9 (index + 15) (index = cube) hacc
  simpa using hcube index hi

theorem sevenHighT0CubeFinalUnitsVal_finalState
    (adj : Fin 49 → Fin 49 → Bool) (cube : Nat)
    (acc : SevenHighT0CubeValState)
    (hstate : acc.1 = sevenHighT0CubePartitionClauses) :
    (sevenHighT0CubeFinalUnitsVal adj cube acc).1 =
      sevenHighT0CubeFinalState cube := by
  rw [sevenHighT0CubeFinalUnitsVal_state, hstate]
  rfl

theorem sevenHighT0CubeNegativePositive_satisfied
    {val : DimacsValuation} {a b : Nat} (hbPos : 0 < b)
    (himp : val a = true → val b = true) :
    dimacsClauseSatisfied val [-(a : Int), (b : Int)] := by
  cases ha : val a
  · exact ⟨-(a : Int), by simp, by simp [dimacsLitValue, ha]⟩
  · refine ⟨(b : Int), by simp, ?_⟩
    simp [dimacsLitValue, hbPos, himp ha]

theorem sevenHighT0CubeNegativePositive_bounded
    {top a b : Nat} (ha : a ≤ top) (hb : b ≤ top) :
    dimacsClauseBounded top [-(a : Int), (b : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl
  · simpa using ha
  · simpa using hb

theorem sevenHighT0CubePositiveList_satisfied
    {val : DimacsValuation} {ids : List Nat}
    (hpos : ∀ id ∈ ids, 0 < id)
    (hwitness : ∃ id ∈ ids, val id = true) :
    dimacsClauseSatisfied val
      (ids.map fun id : Nat => (id : Int)) := by
  obtain ⟨id, hid, htrue⟩ := hwitness
  have hid' : (id : Int) ∈ ids.map (fun id : Nat => (id : Int)) :=
    List.mem_map.mpr ⟨id, hid, rfl⟩
  refine ⟨(id : Int), hid', ?_⟩
  simp [dimacsLitValue, hpos id hid, htrue]

theorem sevenHighT0CubePositiveList_bounded
    {top : Nat} {ids : List Nat} (hids : ∀ id ∈ ids, id ≤ top) :
    dimacsClauseBounded top
      (ids.map fun id : Nat => (id : Int)) := by
  intro lit hlit
  obtain ⟨id, hid, heq⟩ := List.mem_map.mp hlit
  rw [← heq]
  simpa using hids id hid

theorem sevenHighT0CubeNegativeFour_satisfied
    {val : DimacsValuation} {a b c d : Nat}
    (hnot : ¬(val a = true ∧ val b = true ∧
      val c = true ∧ val d = true)) :
    dimacsClauseSatisfied val
      [-(a : Int), -(b : Int), -(c : Int), -(d : Int)] := by
  cases ha : val a
  · exact ⟨-(a : Int), by simp, by simp [dimacsLitValue, ha]⟩
  cases hb : val b
  · exact ⟨-(b : Int), by simp, by simp [dimacsLitValue, hb]⟩
  cases hc : val c
  · exact ⟨-(c : Int), by simp, by simp [dimacsLitValue, hc]⟩
  have hd : val d = false := by
    cases hd' : val d
    · rfl
    · exact False.elim (hnot ⟨ha, hb, hc, hd'⟩)
  exact ⟨-(d : Int), by simp, by simp [dimacsLitValue, hd]⟩

theorem sevenHighT0CubeNegativeFour_bounded
    {top a b c d : Nat}
    (ha : a ≤ top) (hb : b ≤ top) (hc : c ≤ top) (hd : d ≤ top) :
    dimacsClauseBounded top
      [-(a : Int), -(b : Int), -(c : Int), -(d : Int)] := by
  intro lit hlit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
  rcases hlit with rfl | rfl | rfl | rfl
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

abbrev SevenHighT0CubeCommonAccum := List Int × SevenHighT0CubeValState

/-- Semantic counterpart of one iteration of the inner `common` fold. -/
def sevenHighT0CubeCommonWitnessStepVal
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    (input : SevenHighT0CubeCommonAccum) : SevenHighT0CubeCommonAccum :=
  let (common, acc) := sevenHighT0CubeCommonIdVal adj i j w input.2
  let (iw, acc) := sevenHighT0CubeEdgeIdVal adj i w acc
  let (jw, acc) := sevenHighT0CubeEdgeIdVal adj j w acc
  let acc := sevenHighT0CubeEmitVal [-(common : Int), (iw : Int)] acc
  let acc := sevenHighT0CubeEmitVal [-(common : Int), (jw : Int)] acc
  (input.1 ++ [(common : Int)], acc)

/-- Generator-side form of the same inner iteration, split out so subsequent
fold projection proofs remain readable. -/
def sevenHighT0CubeCommonWitnessStep (i j w : Nat)
    (input : List Int × SevenHighT0CubeGenState) :
    List Int × SevenHighT0CubeGenState :=
  let (common, st) := sevenHighT0CubeCommonId i j w input.2
  let (iw, st) := sevenHighT0CubeEdgeId i w st
  let (jw, st) := sevenHighT0CubeEdgeId j w st
  let st := sevenHighT0CubeEmit [-(common : Int), (iw : Int)] st
  let st := sevenHighT0CubeEmit [-(common : Int), (jw : Int)] st
  (input.1 ++ [(common : Int)], st)

theorem sevenHighT0CubeCommonWitnessStep_eq_generator
    (i j w : Nat) (input : List Int × SevenHighT0CubeGenState) :
    sevenHighT0CubeCommonWitnessStep i j w input =
      (let (common, st) := sevenHighT0CubeCommonId i j w input.2
       let (iw, st) := sevenHighT0CubeEdgeId i w st
       let (jw, st) := sevenHighT0CubeEdgeId j w st
       let st := sevenHighT0CubeEmit [-(common : Int), (iw : Int)] st
       let st := sevenHighT0CubeEmit [-(common : Int), (jw : Int)] st
       (input.1 ++ [(common : Int)], st)) := by
  rfl

theorem sevenHighT0CubeCommonWitnessStepVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    (input : SevenHighT0CubeCommonAccum) :
    let out := sevenHighT0CubeCommonWitnessStepVal adj i j w input
    (out.1, out.2.1) =
      sevenHighT0CubeCommonWitnessStep i j w (input.1, input.2.1) := by
  rcases input with ⟨lits, st, val⟩
  simp only [sevenHighT0CubeCommonWitnessStepVal,
    sevenHighT0CubeCommonWitnessStep,
    sevenHighT0CubeCommonIdVal, sevenHighT0CubeEdgeIdVal]
  generalize hc : sevenHighT0CubeCommonId i j w st = commonOut
  rcases commonOut with ⟨common, st1⟩
  generalize hi : sevenHighT0CubeEdgeId i w st1 = iwOut
  rcases iwOut with ⟨iw, st2⟩
  generalize hj : sevenHighT0CubeEdgeId j w st2 = jwOut
  rcases jwOut with ⟨jw, st3⟩
  have hc' : sevenHighT0CubeAtomId (.common i j w) st =
      (common, st1) := hc
  have hi' : sevenHighT0CubeAtomId (.edge (min i w) (max i w)) st1 =
      (iw, st2) := hi
  have hj' : sevenHighT0CubeAtomId (.edge (min j w) (max j w)) st2 =
      (jw, st3) := hj
  simp [sevenHighT0CubeAtomIdVal, hc', hi', hj',
    sevenHighT0CubeEmitVal]

theorem sevenHighT0CubeCommonWitnessStepVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    {input : SevenHighT0CubeCommonAccum}
    (hinput : SevenHighT0CubeSemanticSound adj input.2)
    (hleft : sevenHighT0CubeAtomValue adj (.common i j w) = true →
      sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true)
    (hright : sevenHighT0CubeAtomValue adj (.common i j w) = true →
      sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCommonWitnessStepVal adj i j w input).2 := by
  let a0 := sevenHighT0CubeCommonIdVal adj i j w input.2
  let a1 := sevenHighT0CubeEdgeIdVal adj i w a0.2
  let a2 := sevenHighT0CubeEdgeIdVal adj j w a1.2
  let e1 := sevenHighT0CubeEmitVal
    [-(a0.1 : Int), (a1.1 : Int)] a2.2
  let e2 := sevenHighT0CubeEmitVal
    [-(a0.1 : Int), (a2.1 : Int)] e1
  have hs0 : SevenHighT0CubeSemanticSound adj a0.2 := by
    exact sevenHighT0CubeAtomIdVal_semanticSound adj hinput (.common i j w)
  have hs1 : SevenHighT0CubeSemanticSound adj a1.2 := by
    exact sevenHighT0CubeAtomIdVal_semanticSound adj hs0
      (.edge (min i w) (max i w))
  have hs2 : SevenHighT0CubeSemanticSound adj a2.2 := by
    exact sevenHighT0CubeAtomIdVal_semanticSound adj hs1
      (.edge (min j w) (max j w))
  have hm0a0 : (.common i j w, a0.1) ∈ a0.2.1.ids := by
    exact (sevenHighT0CubeAtomIdVal_result adj (.common i j w)
      input.2.1 input.2.2).1
  have hm0a1 : (.common i j w, a0.1) ∈ a1.2.1.ids := by
    exact sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min i w) (max i w)) a0.2.1 a0.2.2 hm0a0
  have hm0 : (.common i j w, a0.1) ∈ a2.2.1.ids := by
    exact sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2 hm0a1
  have hm1a1 : (.edge (min i w) (max i w), a1.1) ∈ a1.2.1.ids := by
    exact (sevenHighT0CubeAtomIdVal_result adj
      (.edge (min i w) (max i w)) a0.2.1 a0.2.2).1
  have hm1 : (.edge (min i w) (max i w), a1.1) ∈ a2.2.1.ids := by
    exact sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2 hm1a1
  have hm2 : (.edge (min j w) (max j w), a2.1) ∈ a2.2.1.ids := by
    exact (sevenHighT0CubeAtomIdVal_result adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2).1
  have hv0 := hs2.named _ _ hm0
  have hv1 := hs2.named _ _ hm1
  have hv2 := hs2.named _ _ hm2
  have hb0 := (hs2.ids.id_bounds _ hm0)
  have hb1 := (hs2.ids.id_bounds _ hm1)
  have hb2 := (hs2.ids.id_bounds _ hm2)
  have hsE1 : SevenHighT0CubeSemanticSound adj e1 := by
    apply sevenHighT0CubeEmitVal_semanticSound adj hs2
    · apply sevenHighT0CubeNegativePositive_satisfied hb1.1
      intro htrue
      exact hv1.trans (hleft (hv0.symm.trans htrue))
    · exact sevenHighT0CubeNegativePositive_bounded hb0.2 hb1.2
  have hsE2 : SevenHighT0CubeSemanticSound adj e2 := by
    apply sevenHighT0CubeEmitVal_semanticSound adj hsE1
    · apply sevenHighT0CubeNegativePositive_satisfied hb2.1
      intro htrue
      exact hv2.trans (hright (hv0.symm.trans htrue))
    · exact sevenHighT0CubeNegativePositive_bounded hb0.2 hb2.2
  change SevenHighT0CubeSemanticSound adj e2
  exact hsE2

theorem sevenHighT0CubeCommonWitnessStepVal_new_common
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    (input : SevenHighT0CubeCommonAccum) :
    let out := sevenHighT0CubeCommonWitnessStepVal adj i j w input
    ∃ id : Nat, out.1 = input.1 ++ [(id : Int)] ∧
      (.common i j w, id) ∈ out.2.1.ids := by
  let a0 := sevenHighT0CubeCommonIdVal adj i j w input.2
  let a1 := sevenHighT0CubeEdgeIdVal adj i w a0.2
  let a2 := sevenHighT0CubeEdgeIdVal adj j w a1.2
  have hm0 : (.common i j w, a0.1) ∈ a0.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj (.common i j w)
      input.2.1 input.2.2).1
  have hm1 : (.common i j w, a0.1) ∈ a1.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min i w) (max i w)) a0.2.1 a0.2.2 hm0
  have hm2 : (.common i j w, a0.1) ∈ a2.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2 hm1
  refine ⟨a0.1, ?_, ?_⟩
  · rfl
  · exact hm2

theorem sevenHighT0CubeCommonWitnessStepVal_old_mem
    (adj : Fin 49 → Fin 49 → Bool) (i j w : Nat)
    {input : SevenHighT0CubeCommonAccum}
    {entry : SevenHighT0CubeAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (sevenHighT0CubeCommonWitnessStepVal adj i j w input).2.1.ids := by
  let a0 := sevenHighT0CubeCommonIdVal adj i j w input.2
  let a1 := sevenHighT0CubeEdgeIdVal adj i w a0.2
  let a2 := sevenHighT0CubeEdgeIdVal adj j w a1.2
  have hm0 : entry ∈ a0.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj (.common i j w)
      input.2.1 input.2.2 hmem
  have hm1 : entry ∈ a1.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min i w) (max i w)) a0.2.1 a0.2.2 hm0
  have hm2 : entry ∈ a2.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2 hm1
  exact hm2

def sevenHighT0CubeCollectCommonVal
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeCommonAccum :=
  sevenHighT0CubeLows.foldl (fun input w =>
    sevenHighT0CubeCommonWitnessStepVal adj i j w input) ([], acc)

structure SevenHighT0CubeCollectedCommonMatch
    (i j : Nat) (ws : List Nat) (input : SevenHighT0CubeCommonAccum) where
  ids : List Nat
  lits_eq : input.1 = List.map (fun id : Nat => (id : Int)) ids
  aligned : List.Forall₂ (fun w id =>
    ((.common i j w), id) ∈ input.2.1.ids) ws ids

theorem sevenHighT0CubeForall₂_append_singleton
    {α β : Type*} {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) {x : α} {y : β} (hxy : r x y) :
    List.Forall₂ r (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons hxy .nil
  | cons hab hrest ih => exact .cons hab ih

def sevenHighT0CubeCollectedCommonMatch_empty
    (i j : Nat) (acc : SevenHighT0CubeValState) :
    SevenHighT0CubeCollectedCommonMatch i j [] ([], acc) where
  ids := []
  lits_eq := rfl
  aligned := .nil

def sevenHighT0CubeCollectedCommonMatch_push
    (adj : Fin 49 → Fin 49 → Bool) {i j w : Nat} {ws : List Nat}
    {input : SevenHighT0CubeCommonAccum}
    (h : SevenHighT0CubeCollectedCommonMatch i j ws input) :
    SevenHighT0CubeCollectedCommonMatch i j (ws ++ [w])
      (sevenHighT0CubeCommonWitnessStepVal adj i j w input) := by
  let out := sevenHighT0CubeCommonWitnessStepVal adj i j w input
  let a0 := sevenHighT0CubeCommonIdVal adj i j w input.2
  let a1 := sevenHighT0CubeEdgeIdVal adj i w a0.2
  let a2 := sevenHighT0CubeEdgeIdVal adj j w a1.2
  have hlits : out.1 = input.1 ++ [(a0.1 : Int)] := by rfl
  have hm0 : (.common i j w, a0.1) ∈ a0.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj (.common i j w)
      input.2.1 input.2.2).1
  have hm1 : (.common i j w, a0.1) ∈ a1.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min i w) (max i w)) a0.2.1 a0.2.2 hm0
  have hnew : (.common i j w, a0.1) ∈ out.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj
      (.edge (min j w) (max j w)) a1.2.1 a1.2.2 hm1
  refine ⟨h.ids ++ [a0.1], ?_, ?_⟩
  · rw [hlits, h.lits_eq]
    simp
  · have hold : List.Forall₂ (fun z oldId =>
        ((.common i j z), oldId) ∈ out.2.1.ids) ws h.ids := by
      apply h.aligned.imp
      intro z oldId hm
      exact sevenHighT0CubeCommonWitnessStepVal_old_mem adj i j w hm
    exact sevenHighT0CubeForall₂_append_singleton hold hnew

def sevenHighT0CubeCollectCommonVal_match
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState) :
    SevenHighT0CubeCollectedCommonMatch i j sevenHighT0CubeLows
      (sevenHighT0CubeCollectCommonVal adj i j acc) := by
  suffices ∀ pre : List Nat,
      SevenHighT0CubeCollectedCommonMatch i j pre
        (pre.foldl (fun input w =>
          sevenHighT0CubeCommonWitnessStepVal adj i j w input) ([], acc)) by
    exact this sevenHighT0CubeLows
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact sevenHighT0CubeCollectedCommonMatch_empty i j acc
  | append_singleton pre w ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact sevenHighT0CubeCollectedCommonMatch_push adj ih

theorem sevenHighT0CubeForall₂_exists_right_of_mem
    {α β : Type*} {r : α → β → Prop} {xs : List α} {ys : List β}
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

theorem sevenHighT0CubeForall₂_exists_left_of_mem
    {α β : Type*} {r : α → β → Prop} {xs : List α} {ys : List β}
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

theorem sevenHighT0CubeCollectCommonVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCollectCommonVal adj i j acc).2 := by
  unfold sevenHighT0CubeCollectCommonVal
  have hfold : ∀ ws : List Nat, ∀ input : SevenHighT0CubeCommonAccum,
      SevenHighT0CubeSemanticSound adj input.2 →
      (∀ w ∈ ws,
        sevenHighT0CubeAtomValue adj (.common i j w) = true →
          sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true) →
      (∀ w ∈ ws,
        sevenHighT0CubeAtomValue adj (.common i j w) = true →
          sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true) →
      SevenHighT0CubeSemanticSound adj
        (ws.foldl (fun input w =>
          sevenHighT0CubeCommonWitnessStepVal adj i j w input) input).2 := by
    intro ws
    induction ws with
    | nil => intro input hinput _ _; exact hinput
    | cons w ws ih =>
        intro input hinput hl hr
        simp only [List.foldl_cons]
        apply ih
        · exact sevenHighT0CubeCommonWitnessStepVal_semanticSound adj i j w
            hinput (hl w (by simp)) (hr w (by simp))
        · intro x hx
          exact hl x (by simp [hx])
        · intro x hx
          exact hr x (by simp [hx])
  exact hfold sevenHighT0CubeLows ([], acc) hacc hleft hright

theorem sevenHighT0CubeCollectCommonVal_bounded
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true) :
    let common := sevenHighT0CubeCollectCommonVal adj i j acc
    dimacsClauseBounded common.2.1.top common.1 := by
  dsimp only
  have hm : SevenHighT0CubeCollectedCommonMatch i j sevenHighT0CubeLows
      (sevenHighT0CubeCollectCommonVal adj i j acc) :=
    sevenHighT0CubeCollectCommonVal_match adj i j acc
  have hs : SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCollectCommonVal adj i j acc).2 :=
    sevenHighT0CubeCollectCommonVal_semanticSound adj i j hacc hleft hright
  intro lit hlit
  rw [hm.lits_eq] at hlit
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hlit
  obtain ⟨w, hw, hatom⟩ :=
    sevenHighT0CubeForall₂_exists_left_of_mem hm.aligned hid
  simpa using (hs.ids.id_bounds _ hatom).2

theorem sevenHighT0CubeCollectCommonVal_positive
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true →
        sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true)
    (hwitness : ∃ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common i j w) = true) :
    let common := sevenHighT0CubeCollectCommonVal adj i j acc
    dimacsClauseSatisfied common.2.2 common.1 := by
  dsimp only
  have hm : SevenHighT0CubeCollectedCommonMatch i j sevenHighT0CubeLows
      (sevenHighT0CubeCollectCommonVal adj i j acc) :=
    sevenHighT0CubeCollectCommonVal_match adj i j acc
  have hs : SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCollectCommonVal adj i j acc).2 :=
    sevenHighT0CubeCollectCommonVal_semanticSound adj i j hacc hleft hright
  obtain ⟨w, hw, htrue⟩ := hwitness
  obtain ⟨id, hid, hatom⟩ :=
    sevenHighT0CubeForall₂_exists_right_of_mem hm.aligned hw
  have hlit : (id : Int) ∈
      (sevenHighT0CubeCollectCommonVal adj i j acc).1 := by
    rw [hm.lits_eq]
    exact List.mem_map.mpr ⟨id, hid, rfl⟩
  have hpos := (hs.ids.id_bounds _ hatom).1
  have hval := (hs.named _ _ hatom).trans htrue
  refine ⟨(id : Int), hlit, ?_⟩
  simp [dimacsLitValue, hpos, hval]

def sevenHighT0CubeCollectCommon (i j : Nat)
    (st : SevenHighT0CubeGenState) : List Int × SevenHighT0CubeGenState :=
  sevenHighT0CubeLows.foldl (fun input w =>
    sevenHighT0CubeCommonWitnessStep i j w input) ([], st)

theorem sevenHighT0CubeCommonFold_projection
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat) (ws : List Nat)
    (input : SevenHighT0CubeCommonAccum) :
    let outVal := ws.foldl (fun input w =>
      sevenHighT0CubeCommonWitnessStepVal adj i j w input) input
    let outGen := ws.foldl (fun input w =>
      sevenHighT0CubeCommonWitnessStep i j w input)
      (input.1, input.2.1)
    (outVal.1, outVal.2.1) = outGen := by
  induction ws generalizing input with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.foldl_cons]
      let nextVal := sevenHighT0CubeCommonWitnessStepVal adj i j w input
      have hstep := sevenHighT0CubeCommonWitnessStepVal_projection
        adj i j w input
      have hrest := ih nextVal
      change (nextVal.1, nextVal.2.1) =
        sevenHighT0CubeCommonWitnessStep i j w
          (input.1, input.2.1) at hstep
      rw [hstep] at hrest
      exact hrest

theorem sevenHighT0CubeCollectCommonVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (i j : Nat)
    (acc : SevenHighT0CubeValState) :
    let out := sevenHighT0CubeCollectCommonVal adj i j acc
    (out.1, out.2.1) = sevenHighT0CubeCollectCommon i j acc.1 := by
  simpa only [sevenHighT0CubeCollectCommonVal,
    sevenHighT0CubeCollectCommon] using
    (sevenHighT0CubeCommonFold_projection adj i j
      sevenHighT0CubeLows ([], acc))

def sevenHighT0CubeCommonPairStepVal
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let common := sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc
  sevenHighT0CubeEmitVal common.1 common.2

theorem sevenHighT0CubeCommonPairStepVal_eq
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    (acc : SevenHighT0CubeValState) :
    sevenHighT0CubeCommonPairStepVal adj pair acc =
      sevenHighT0CubeEmitVal
        (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).1
        (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2 := by
  rfl

theorem sevenHighT0CubeCommonPairStepVal_state
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeCommonPairStepVal adj pair acc).1 =
      sevenHighT0CubeCommonPairStep pair acc.1 := by
  have hp :
      ((sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).1,
        (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2.1) =
        sevenHighT0CubeCollectCommon pair.1 pair.2 acc.1 :=
    sevenHighT0CubeCollectCommonVal_projection adj pair.1 pair.2 acc
  have hem := congrArg (fun p : List Int × SevenHighT0CubeGenState =>
    sevenHighT0CubeEmit p.1 p.2) hp
  simpa only [sevenHighT0CubeCommonPairStepVal, sevenHighT0CubeEmitVal,
    sevenHighT0CubeCommonPairStep,
    sevenHighT0CubeCollectCommon, sevenHighT0CubeCommonWitnessStep] using hem

theorem sevenHighT0CubeCommonPairStepVal_emit_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.1 w) (max pair.1 w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.2 w) (max pair.2 w)) = true)
    (hpositive : dimacsClauseSatisfied
      (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2.2
      (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).1)
    (hbounded : dimacsClauseBounded
      (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2.1.top
      (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).1) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeEmitVal
        (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).1
        (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2) := by
  have hs : SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc).2 :=
    sevenHighT0CubeCollectCommonVal_semanticSound adj pair.1 pair.2
      (acc := acc) hacc hleft hright
  generalize hcommon :
    sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc = common at *
  rcases common with ⟨clause, st, val⟩
  exact sevenHighT0CubeEmitVal_semanticSound adj hs
    clause hpositive hbounded

theorem sevenHighT0CubeCommonPairStepVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.1 w) (max pair.1 w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.2 w) (max pair.2 w)) = true)
    (hpositive : let common :=
        sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc
      dimacsClauseSatisfied common.2.2 common.1)
    (hbounded : let common :=
        sevenHighT0CubeCollectCommonVal adj pair.1 pair.2 acc
      dimacsClauseBounded common.2.1.top common.1) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCommonPairStepVal adj pair acc) := by
  rw [sevenHighT0CubeCommonPairStepVal_eq]
  exact sevenHighT0CubeCommonPairStepVal_emit_semanticSound adj pair
    hacc hleft hright hpositive hbounded

set_option maxHeartbeats 1000000 in
theorem sevenHighT0CubeCommonPairStepVal_semanticSound_of_witness
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.1 w) (max pair.1 w)) = true)
    (hright : ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.2 w) (max pair.2 w)) = true)
    (hwitness : ∃ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCommonPairStepVal adj pair acc) := by
  apply sevenHighT0CubeCommonPairStepVal_semanticSound adj pair hacc
    hleft hright
  · exact sevenHighT0CubeCollectCommonVal_positive adj pair.1 pair.2 acc
      hacc hleft hright hwitness
  · exact sevenHighT0CubeCollectCommonVal_bounded adj pair.1 pair.2 acc
      hacc hleft hright

def sevenHighT0CubeCommonClausesFromVal
    (adj : Fin 49 → Fin 49 → Bool)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  (sevenHighT0CubePairs sevenHighT0CubeHighs).foldl (fun acc pair =>
    sevenHighT0CubeCommonPairStepVal adj pair acc) acc

theorem sevenHighT0CubeCommonClausesFromVal_state
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeCommonClausesFromVal adj acc).1 =
      (sevenHighT0CubePairs sevenHighT0CubeHighs).foldl
        (fun st pair => sevenHighT0CubeCommonPairStep pair st) acc.1 := by
  unfold sevenHighT0CubeCommonClausesFromVal
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun pair acc => sevenHighT0CubeCommonPairStepVal_state adj pair acc)

theorem sevenHighT0CubeCommonClausesFromVal_generatorState
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState)
    (hstate : acc.1 = sevenHighT0CubeNormalizeN1) :
    (sevenHighT0CubeCommonClausesFromVal adj acc).1 =
      sevenHighT0CubeCommonClauses := by
  rw [sevenHighT0CubeCommonClausesFromVal_state, hstate]
  rfl

set_option maxHeartbeats 1000000 in
theorem sevenHighT0CubeCommonClausesFromVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hleft : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.1 w) (max pair.1 w)) = true)
    (hright : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      ∀ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true →
        sevenHighT0CubeAtomValue adj
          (.edge (min pair.2 w) (max pair.2 w)) = true)
    (hwitness : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      ∃ w ∈ sevenHighT0CubeLows,
        sevenHighT0CubeAtomValue adj (.common pair.1 pair.2 w) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCommonClausesFromVal adj acc) := by
  unfold sevenHighT0CubeCommonClausesFromVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro pair hp acc hacc
  exact sevenHighT0CubeCommonPairStepVal_semanticSound_of_witness
    adj pair hacc (hleft pair hp) (hright pair hp) (hwitness pair hp)

def sevenHighT0CubeC4WitnessPairVal
    (adj : Fin 49 → Fin 49 → Bool) (i j w w' : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let (iw, acc) := sevenHighT0CubeEdgeIdVal adj i w acc
  let (jw, acc) := sevenHighT0CubeEdgeIdVal adj j w acc
  let (iw', acc) := sevenHighT0CubeEdgeIdVal adj i w' acc
  let (jw', acc) := sevenHighT0CubeEdgeIdVal adj j w' acc
  sevenHighT0CubeEmitVal
    [-(iw : Int), -(jw : Int), -(iw' : Int), -(jw' : Int)] acc

def sevenHighT0CubeC4WitnessPair (i j w w' : Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let (iw, st) := sevenHighT0CubeEdgeId i w st
  let (jw, st) := sevenHighT0CubeEdgeId j w st
  let (iw', st) := sevenHighT0CubeEdgeId i w' st
  let (jw', st) := sevenHighT0CubeEdgeId j w' st
  sevenHighT0CubeEmit
    [-(iw : Int), -(jw : Int), -(iw' : Int), -(jw' : Int)] st

theorem sevenHighT0CubeC4WitnessPairVal_state
    (adj : Fin 49 → Fin 49 → Bool) (i j w w' : Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeC4WitnessPairVal adj i j w w' acc).1 =
      sevenHighT0CubeC4WitnessPair i j w w' acc.1 := by
  rcases acc with ⟨st, val⟩
  simp only [sevenHighT0CubeC4WitnessPairVal,
    sevenHighT0CubeC4WitnessPair, sevenHighT0CubeEdgeIdVal]
  generalize h0 : sevenHighT0CubeEdgeId i w st = out0
  rcases out0 with ⟨id0, st0⟩
  generalize h1 : sevenHighT0CubeEdgeId j w st0 = out1
  rcases out1 with ⟨id1, st1⟩
  generalize h2 : sevenHighT0CubeEdgeId i w' st1 = out2
  rcases out2 with ⟨id2, st2⟩
  generalize h3 : sevenHighT0CubeEdgeId j w' st2 = out3
  rcases out3 with ⟨id3, st3⟩
  have h0' : sevenHighT0CubeAtomId (.edge (min i w) (max i w)) st =
      (id0, st0) := h0
  have h1' : sevenHighT0CubeAtomId (.edge (min j w) (max j w)) st0 =
      (id1, st1) := h1
  have h2' : sevenHighT0CubeAtomId (.edge (min i w') (max i w')) st1 =
      (id2, st2) := h2
  have h3' : sevenHighT0CubeAtomId (.edge (min j w') (max j w')) st2 =
      (id3, st3) := h3
  simp [sevenHighT0CubeAtomIdVal, h0', h1', h2', h3',
    sevenHighT0CubeEmitVal]

theorem sevenHighT0CubeC4WitnessPairVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (i j w w' : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hnot : ¬(
      sevenHighT0CubeAtomValue adj (.edge (min i w) (max i w)) = true ∧
      sevenHighT0CubeAtomValue adj (.edge (min j w) (max j w)) = true ∧
      sevenHighT0CubeAtomValue adj (.edge (min i w') (max i w')) = true ∧
      sevenHighT0CubeAtomValue adj (.edge (min j w') (max j w')) = true)) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeC4WitnessPairVal adj i j w w' acc) := by
  let atom0 := SevenHighT0CubeAtom.edge (min i w) (max i w)
  let atom1 := SevenHighT0CubeAtom.edge (min j w) (max j w)
  let atom2 := SevenHighT0CubeAtom.edge (min i w') (max i w')
  let atom3 := SevenHighT0CubeAtom.edge (min j w') (max j w')
  let a0 := sevenHighT0CubeAtomIdVal adj atom0 acc
  let a1 := sevenHighT0CubeAtomIdVal adj atom1 a0.2
  let a2 := sevenHighT0CubeAtomIdVal adj atom2 a1.2
  let a3 := sevenHighT0CubeAtomIdVal adj atom3 a2.2
  have hs0 := sevenHighT0CubeAtomIdVal_semanticSound adj hacc atom0
  have hs1 := sevenHighT0CubeAtomIdVal_semanticSound adj hs0 atom1
  have hs2 := sevenHighT0CubeAtomIdVal_semanticSound adj hs1 atom2
  have hs3 := sevenHighT0CubeAtomIdVal_semanticSound adj hs2 atom3
  have hm0a0 : (atom0, a0.1) ∈ a0.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj atom0 acc.1 acc.2).1
  have hm0a1 : (atom0, a0.1) ∈ a1.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom1 a0.2.1 a0.2.2 hm0a0
  have hm0a2 : (atom0, a0.1) ∈ a2.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom2 a1.2.1 a1.2.2 hm0a1
  have hm0 : (atom0, a0.1) ∈ a3.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom3 a2.2.1 a2.2.2 hm0a2
  have hm1a1 : (atom1, a1.1) ∈ a1.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj atom1 a0.2.1 a0.2.2).1
  have hm1a2 : (atom1, a1.1) ∈ a2.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom2 a1.2.1 a1.2.2 hm1a1
  have hm1 : (atom1, a1.1) ∈ a3.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom3 a2.2.1 a2.2.2 hm1a2
  have hm2a2 : (atom2, a2.1) ∈ a2.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj atom2 a1.2.1 a1.2.2).1
  have hm2 : (atom2, a2.1) ∈ a3.2.1.ids :=
    sevenHighT0CubeAtomIdVal_old_mem adj atom3 a2.2.1 a2.2.2 hm2a2
  have hm3 : (atom3, a3.1) ∈ a3.2.1.ids :=
    (sevenHighT0CubeAtomIdVal_result adj atom3 a2.2.1 a2.2.2).1
  have hv0 := hs3.named _ _ hm0
  have hv1 := hs3.named _ _ hm1
  have hv2 := hs3.named _ _ hm2
  have hv3 := hs3.named _ _ hm3
  have hb0 := (hs3.ids.id_bounds _ hm0)
  have hb1 := (hs3.ids.id_bounds _ hm1)
  have hb2 := (hs3.ids.id_bounds _ hm2)
  have hb3 := (hs3.ids.id_bounds _ hm3)
  unfold sevenHighT0CubeC4WitnessPairVal
  apply sevenHighT0CubeEmitVal_semanticSound adj hs3
  · apply sevenHighT0CubeNegativeFour_satisfied
    intro hall
    apply hnot
    exact ⟨hv0.symm.trans hall.1,
      hv1.symm.trans hall.2.1,
      hv2.symm.trans hall.2.2.1,
      hv3.symm.trans hall.2.2.2⟩
  · exact sevenHighT0CubeNegativeFour_bounded
      hb0.2 hb1.2 hb2.2 hb3.2

def sevenHighT0CubeC4PairStepVal
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let others := sevenHighT0CubeVertices.filter fun w =>
    w ≠ pair.1 && w ≠ pair.2
  (sevenHighT0CubePairs others).foldl (fun acc witnesses =>
    sevenHighT0CubeC4WitnessPairVal adj pair.1 pair.2
      witnesses.1 witnesses.2 acc) acc

theorem sevenHighT0CubeC4PairStepVal_state
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeC4PairStepVal adj pair acc).1 =
      sevenHighT0CubeC4PairStep pair acc.1 := by
  unfold sevenHighT0CubeC4PairStepVal sevenHighT0CubeC4PairStep
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun witnesses acc =>
      sevenHighT0CubeC4WitnessPairVal_state adj pair.1 pair.2
        witnesses.1 witnesses.2 acc)

theorem sevenHighT0CubeC4PairStepVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (pair : Nat × Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hnot : ∀ witnesses ∈ sevenHighT0CubePairs
        (sevenHighT0CubeVertices.filter fun w =>
          w ≠ pair.1 && w ≠ pair.2), ¬(
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 witnesses.1) (max pair.1 witnesses.1)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.2 witnesses.1) (max pair.2 witnesses.1)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 witnesses.2) (max pair.1 witnesses.2)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.2 witnesses.2) (max pair.2 witnesses.2)) = true)) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeC4PairStepVal adj pair acc) := by
  unfold sevenHighT0CubeC4PairStepVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro witnesses hw acc hacc
  exact sevenHighT0CubeC4WitnessPairVal_semanticSound adj pair.1 pair.2
    witnesses.1 witnesses.2 hacc (hnot witnesses hw)

def sevenHighT0CubeC4ClausesFromVal
    (adj : Fin 49 → Fin 49 → Bool)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  (sevenHighT0CubePairs sevenHighT0CubeVertices).foldl (fun acc pair =>
    sevenHighT0CubeC4PairStepVal adj pair acc) acc

theorem sevenHighT0CubeC4ClausesFromVal_state
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeC4ClausesFromVal adj acc).1 =
      (sevenHighT0CubePairs sevenHighT0CubeVertices).foldl
        (fun st pair => sevenHighT0CubeC4PairStep pair st) acc.1 := by
  unfold sevenHighT0CubeC4ClausesFromVal
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun pair acc => sevenHighT0CubeC4PairStepVal_state adj pair acc)

theorem sevenHighT0CubeC4ClausesFromVal_generatorState
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState)
    (hstate : acc.1 = sevenHighT0CubeCommonClauses) :
    (sevenHighT0CubeC4ClausesFromVal adj acc).1 =
      sevenHighT0CubeC4Clauses := by
  rw [sevenHighT0CubeC4ClausesFromVal_state, hstate]
  rfl

theorem sevenHighT0CubeC4ClausesFromVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hnot : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeVertices,
      ∀ witnesses ∈ sevenHighT0CubePairs
        (sevenHighT0CubeVertices.filter fun w =>
          w ≠ pair.1 && w ≠ pair.2), ¬(
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 witnesses.1) (max pair.1 witnesses.1)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.2 witnesses.1) (max pair.2 witnesses.1)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.1 witnesses.2) (max pair.1 witnesses.2)) = true ∧
      sevenHighT0CubeAtomValue adj
        (.edge (min pair.2 witnesses.2) (max pair.2 witnesses.2)) = true)) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeC4ClausesFromVal adj acc) := by
  unfold sevenHighT0CubeC4ClausesFromVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro pair hp acc hacc
  exact sevenHighT0CubeC4PairStepVal_semanticSound adj pair hacc
    (hnot pair hp)

def sevenHighT0CubeLiteralRow (val : DimacsValuation) (vars : Array Int) :
    Fin vars.size → Bool := fun i => dimacsLitValue val (vars.getD i.val 0)

structure SevenHighT0CubeInputAccumSound
    (adj : Fin 49 → Fin 49 → Bool)
    (input : Array Int × SevenHighT0CubeValState) : Prop where
  semantic : SevenHighT0CubeSemanticSound adj input.2
  nonzero : ∀ lit ∈ input.1, lit ≠ 0
  bounded : ∀ lit ∈ input.1, lit.natAbs ≤ input.2.1.top

theorem sevenHighT0CubeInputAccumSound_empty
    (adj : Fin 49 → Fin 49 → Bool) {acc : SevenHighT0CubeValState}
    (h : SevenHighT0CubeSemanticSound adj acc) :
    SevenHighT0CubeInputAccumSound adj (#[], acc) where
  semantic := h
  nonzero := by simp
  bounded := by simp

theorem sevenHighT0CubeAtomId_top_le
    (atom : SevenHighT0CubeAtom) (st : SevenHighT0CubeGenState) :
    st.top ≤ (sevenHighT0CubeAtomId atom st).2.top := by
  unfold sevenHighT0CubeAtomId
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ _

def sevenHighT0CubeCollectEdgeVal
    (adj : Fin 49 → Fin 49 → Bool) (y x : Nat)
    (input : Array Int × SevenHighT0CubeValState) :
    Array Int × SevenHighT0CubeValState :=
  let (id, acc) := sevenHighT0CubeEdgeIdVal adj y x input.2
  (input.1.push (id : Int), acc)

structure SevenHighT0CubeCollectedEdgesMatch
    (y : Nat) (xs : List Nat)
    (input : Array Int × SevenHighT0CubeValState) where
  ids : List Nat
  vars_eq : input.1.toList = List.map (fun id : Nat => Int.ofNat id) ids
  aligned : List.Forall₂ (fun x id =>
    ((.edge (min y x) (max y x)), id) ∈ input.2.1.ids) xs ids

def sevenHighT0CubeCollectedEdgesMatch_empty
    (y : Nat) (acc : SevenHighT0CubeValState) :
    SevenHighT0CubeCollectedEdgesMatch y [] (#[], acc) where
  ids := []
  vars_eq := rfl
  aligned := .nil

def sevenHighT0CubeCollectedEdgesMatch_push
    (adj : Fin 49 → Fin 49 → Bool)
    {y x : Nat} {xs : List Nat}
    {input : Array Int × SevenHighT0CubeValState}
    (h : SevenHighT0CubeCollectedEdgesMatch y xs input) :
    SevenHighT0CubeCollectedEdgesMatch y (xs ++ [x])
      (sevenHighT0CubeCollectEdgeVal adj y x input) := by
  rcases input with ⟨vars, acc⟩
  simp only [sevenHighT0CubeCollectEdgeVal, sevenHighT0CubeEdgeIdVal]
  generalize hout : sevenHighT0CubeAtomIdVal adj
    (.edge (min y x) (max y x)) acc = out
  rcases out with ⟨id, acc'⟩
  refine ⟨h.ids ++ [id], ?_, ?_⟩
  · rw [Array.toList_push, h.vars_eq]
    simp
  · have hold : List.Forall₂ (fun z oldId =>
        ((.edge (min y z) (max y z)), oldId) ∈ acc'.1.ids) xs h.ids := by
      apply h.aligned.imp
      intro z oldId hm
      have hx := sevenHighT0CubeAtomIdVal_old_mem adj
        (.edge (min y x) (max y x)) acc.1 acc.2 hm
      rw [hout] at hx
      exact hx
    have hnew := (sevenHighT0CubeAtomIdVal_result adj
      (.edge (min y x) (max y x)) acc.1 acc.2).1
    rw [hout] at hnew
    exact sevenHighT0CubeForall₂_append_singleton hold hnew

def sevenHighT0CubeCollectEdgesListVal_match
    (adj : Fin 49 → Fin 49 → Bool) (y : Nat) (xs : List Nat)
    (acc : SevenHighT0CubeValState) :
    SevenHighT0CubeCollectedEdgesMatch y xs
      (xs.foldl (fun input x =>
        sevenHighT0CubeCollectEdgeVal adj y x input) (#[], acc)) := by
  suffices ∀ pre : List Nat,
      SevenHighT0CubeCollectedEdgesMatch y pre
        (pre.foldl (fun input x =>
          sevenHighT0CubeCollectEdgeVal adj y x input) (#[], acc)) by
    exact this xs
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact sevenHighT0CubeCollectedEdgesMatch_empty y acc
  | append_singleton pre x ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact sevenHighT0CubeCollectedEdgesMatch_push adj ih

theorem sevenHighT0CubeCollectedEdgesMatch_length
    {y : Nat} {xs : List Nat}
    {input : Array Int × SevenHighT0CubeValState}
    (h : SevenHighT0CubeCollectedEdgesMatch y xs input) :
    input.1.size = xs.length := by
  have hvars := congrArg List.length h.vars_eq
  have halign := h.aligned.length_eq
  simpa using hvars.trans (by simpa using halign.symm)

theorem sevenHighT0CubeCollectedEdgesMatch_value
    (adj : Fin 49 → Fin 49 → Bool)
    {y : Nat} {xs : List Nat}
    {input : Array Int × SevenHighT0CubeValState}
    (h : SevenHighT0CubeCollectedEdgesMatch y xs input)
    (hs : SevenHighT0CubeSemanticSound adj input.2)
    (i : Nat) (hi : i < input.1.size) :
    dimacsLitValue input.2.2 (input.1.getD i 0) =
      sevenHighT0CubeAtomValue adj
        (.edge (min y (xs.get ⟨i, by
          rw [← sevenHighT0CubeCollectedEdgesMatch_length h]; exact hi⟩))
          (max y (xs.get ⟨i, by
            rw [← sevenHighT0CubeCollectedEdgesMatch_length h]; exact hi⟩))) := by
  have hidsLen : h.ids.length = xs.length := h.aligned.length_eq.symm
  have hiIds : i < h.ids.length := by
    rw [hidsLen, ← sevenHighT0CubeCollectedEdgesMatch_length h]
    exact hi
  have hiXs : i < xs.length := by
    rw [← sevenHighT0CubeCollectedEdgesMatch_length h]
    exact hi
  have halign := h.aligned.get hiXs hiIds
  have hiList : i < input.1.toList.length := by simpa using hi
  have hlistGet : input.1.toList[i] =
      (h.ids.get ⟨i, hiIds⟩ : Int) := by
    have hx := List.get_of_eq h.vars_eq ⟨i, hiList⟩
    rw [List.get_eq_getElem] at hx
    have hiMap : i <
        (List.map (fun id : Nat => Int.ofNat id) h.ids).length := by
      simpa using hiIds
    calc
      input.1.toList[i] =
          (List.map (fun id : Nat => Int.ofNat id) h.ids)[i]'hiMap := hx
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

theorem sevenHighT0CubeSeqPrefixTrue_literalRow_eq_count
    (val : DimacsValuation) (vars : Array Int) :
    seqPrefixTrue (sevenHighT0CubeLiteralRow val vars) vars.size =
      (List.ofFn (sevenHighT0CubeLiteralRow val vars)).count true := by
  rw [seqPrefixTrue_full_eq_filter_card]
  let v : List.Vector Bool vars.size :=
    ⟨List.ofFn (sevenHighT0CubeLiteralRow val vars), by simp⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  convert h using 1 <;> simp [v, List.Vector.get]

theorem sevenHighT0CubeSeqPrefixTrue_eq_count
    {n : Nat} (x : Fin n → Bool) :
    seqPrefixTrue x n = (List.ofFn x).count true := by
  rw [seqPrefixTrue_full_eq_filter_card]
  let v : List.Vector Bool n := ⟨List.ofFn x, by simp⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  convert h using 1 <;> simp [v, List.Vector.get]

theorem sevenHighT0CubeCollectedEdges_values
    (adj : Fin 49 → Fin 49 → Bool)
    {y : Nat} {xs : List Nat}
    {input : Array Int × SevenHighT0CubeValState}
    (hm : SevenHighT0CubeCollectedEdgesMatch y xs input)
    (hs : SevenHighT0CubeSemanticSound adj input.2) :
    List.ofFn (sevenHighT0CubeLiteralRow input.2.2 input.1) =
      xs.map (fun x => sevenHighT0CubeAtomValue adj
        (.edge (min y x) (max y x))) := by
  apply List.ext_getElem
  · simp [sevenHighT0CubeCollectedEdgesMatch_length hm]
  · intro i hiLeft hiRight
    have hi : i < input.1.size := by simpa using hiLeft
    have hv := sevenHighT0CubeCollectedEdgesMatch_value adj hm hs i hi
    simpa [List.getElem_ofFn, sevenHighT0CubeLiteralRow] using hv

theorem sevenHighT0CubeCollectEdgeVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (y x : Nat)
    (input : Array Int × SevenHighT0CubeValState) :
    let out := sevenHighT0CubeCollectEdgeVal adj y x input
    let raw :=
      let (id, st) := sevenHighT0CubeEdgeId y x input.2.1
      (input.1.push (id : Int), st)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  rcases input with ⟨vars, st, val⟩
  simp only [sevenHighT0CubeCollectEdgeVal, sevenHighT0CubeEdgeIdVal,
    sevenHighT0CubeEdgeId]
  generalize hv : sevenHighT0CubeAtomIdVal adj
    (.edge (min y x) (max y x)) (st, val) = outVal
  rcases outVal with ⟨idVal, stVal, val'⟩
  generalize hs : sevenHighT0CubeAtomId
    (.edge (min y x) (max y x)) st = out
  rcases out with ⟨id, st'⟩
  have hid := sevenHighT0CubeAtomIdVal_id adj
    (.edge (min y x) (max y x)) st val
  have hstate := sevenHighT0CubeAtomIdVal_state adj
    (.edge (min y x) (max y x)) st val
  rw [hv, hs] at hid hstate
  exact ⟨by simp_all, by simp_all⟩

theorem sevenHighT0CubeCollectEdgesListVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (y : Nat) (xs : List Nat)
    (input : Array Int × SevenHighT0CubeValState) :
    let out := xs.foldl
      (fun input x => sevenHighT0CubeCollectEdgeVal adj y x input) input
    let raw := xs.foldl (fun input x =>
      let (id, st) := sevenHighT0CubeEdgeId y x input.2
      (input.1.push (id : Int), st)) (input.1, input.2.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  induction xs generalizing input with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hp := sevenHighT0CubeCollectEdgeVal_projection adj y x input
      have hi := ih (sevenHighT0CubeCollectEdgeVal adj y x input)
      rcases hp with ⟨hvars, hst⟩
      simpa [hvars, hst] using hi

theorem sevenHighT0CubeCollectEdgeVal_sound
    (adj : Fin 49 → Fin 49 → Bool)
    {input : Array Int × SevenHighT0CubeValState}
    (h : SevenHighT0CubeInputAccumSound adj input) (y x : Nat) :
    SevenHighT0CubeInputAccumSound adj
      (sevenHighT0CubeCollectEdgeVal adj y x input) := by
  rcases input with ⟨vars, st, val⟩
  simp only [sevenHighT0CubeCollectEdgeVal, sevenHighT0CubeEdgeIdVal]
  generalize hout : sevenHighT0CubeAtomIdVal adj
    (.edge (min y x) (max y x)) (st, val) = out
  rcases out with ⟨id, acc'⟩
  have hs := sevenHighT0CubeAtomIdVal_semanticSound adj h.semantic
    (.edge (min y x) (max y x))
  rw [hout] at hs
  have hr := sevenHighT0CubeAtomIdVal_result adj
    (.edge (min y x) (max y x)) st val
  rw [hout] at hr
  dsimp at hr
  have hstate := sevenHighT0CubeAtomIdVal_state adj
    (.edge (min y x) (max y x)) st val
  rw [hout] at hstate
  have htop : st.top ≤ acc'.1.top := by
    rw [hstate]
    exact sevenHighT0CubeAtomId_top_le _ st
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

def sevenHighT0CubeInputAccumRow
    (input : Array Int × SevenHighT0CubeValState) :
    Fin input.1.size → Bool :=
  sevenHighT0CubeLiteralRow input.2.2 input.1

theorem sevenHighT0CubeInputAccum_reifies
    (adj : Fin 49 → Fin 49 → Bool)
    {input : Array Int × SevenHighT0CubeValState}
    (h : SevenHighT0CubeInputAccumSound adj input) :
    SeqCounterInputReifies input.2.2 input.2.1.top input.1
      (sevenHighT0CubeInputAccumRow input) where
  size_eq := rfl
  nonzero := by
    intro i hi
    apply h.nonzero
    rw [show input.1.getD i 0 = input.1[i] by simp [Array.getD, hi]]
    exact Array.getElem_mem hi
  bounded := by
    intro i hi
    apply h.bounded
    rw [show input.1.getD i 0 = input.1[i] by simp [Array.getD, hi]]
    exact Array.getElem_mem hi
  value := by
    intro i hi
    rfl

def sevenHighT0CubeCollectDegreeInputsVal
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState) :
    Array Int × SevenHighT0CubeValState :=
  let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
  incident.foldl (fun input x =>
    sevenHighT0CubeCollectEdgeVal adj vertex x input) (#[], acc)

theorem sevenHighT0CubeCollectDegreeInputsVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState) :
    let out := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
    let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
    let raw := incident.foldl (fun input x =>
      let (id, st) := sevenHighT0CubeEdgeId vertex x input.2
      (input.1.push (id : Int), st)) (#[], acc.1)
    out.1 = raw.1 ∧ out.2.1 = raw.2 := by
  unfold sevenHighT0CubeCollectDegreeInputsVal
  exact sevenHighT0CubeCollectEdgesListVal_projection adj vertex _ (#[], acc)

def sevenHighT0CubeCollectDegreeInputsVal_match
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState) :
    SevenHighT0CubeCollectedEdgesMatch vertex
      (sevenHighT0CubeVertices.filter fun x => x ≠ vertex)
      (sevenHighT0CubeCollectDegreeInputsVal adj vertex acc) := by
  exact sevenHighT0CubeCollectEdgesListVal_match adj vertex _ acc

theorem sevenHighT0CubeCollectDegreeInputsVal_sound
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc) :
    SevenHighT0CubeInputAccumSound adj
      (sevenHighT0CubeCollectDegreeInputsVal adj vertex acc) := by
  unfold sevenHighT0CubeCollectDegreeInputsVal
  let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
  have hfold : ∀ xs : List Nat,
      ∀ input : Array Int × SevenHighT0CubeValState,
      SevenHighT0CubeInputAccumSound adj input →
      SevenHighT0CubeInputAccumSound adj
        (xs.foldl (fun input x =>
          sevenHighT0CubeCollectEdgeVal adj vertex x input) input) := by
    intro xs
    induction xs with
    | nil => exact fun _ h => h
    | cons x xs ih =>
        intro input hinput
        simp only [List.foldl_cons]
        exact ih _ (sevenHighT0CubeCollectEdgeVal_sound adj hinput vertex x)
  exact hfold incident (#[], acc)
    (sevenHighT0CubeInputAccumSound_empty adj hacc)

theorem sevenHighT0CubeCollectDegreeInputsVal_count_atoms
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound adj acc) :
    let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
    seqPrefixTrue (sevenHighT0CubeInputAccumRow input) input.1.size =
      ((sevenHighT0CubeVertices.filter fun x => x ≠ vertex).map fun x =>
        sevenHighT0CubeAtomValue adj
          (.edge (min vertex x) (max vertex x))).count true := by
  let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
  let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
  have hm := sevenHighT0CubeCollectDegreeInputsVal_match adj vertex acc
  have hs := (sevenHighT0CubeCollectDegreeInputsVal_sound adj vertex hacc).semantic
  have hvalues := sevenHighT0CubeCollectedEdges_values adj hm hs
  calc
    seqPrefixTrue (sevenHighT0CubeInputAccumRow input) input.1.size =
        (List.ofFn (sevenHighT0CubeLiteralRow input.2.2 input.1)).count true :=
      sevenHighT0CubeSeqPrefixTrue_literalRow_eq_count input.2.2 input.1
    _ = (incident.map fun x => sevenHighT0CubeAtomValue adj
          (.edge (min vertex x) (max vertex x))).count true :=
      congrArg (List.count true) hvalues

theorem sevenHighT0CubeIncidentList_eq_otherVertices (vertex : Fin 49) :
    sevenHighT0CubeVertices.filter (fun x => x ≠ vertex.val) =
      List.ofFn (fun k : Fin 48 =>
        (orderFortyNineOtherVertex vertex k).val) := by
  native_decide +revert

theorem sevenHighT0CubeAtomValue_edge_bitAdj
    (edges : BitVec 1176) (i j : Fin 49) :
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min i.val j.val) (max i.val j.val)) =
      orderFortyNineBitAdj edges i j := by
  by_cases hij : i = j
  · subst j
    simp [sevenHighT0CubeAtomValue, orderFortyNineBitAdj]
  · simp only [sevenHighT0CubeAtomValue]
    split <;> rename_i hmin
    · split <;> rename_i hmax
      · simp only [orderFortyNineBitAdj, hij, if_false]
        congr 1
        have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [orderFortyNineEdgeIndex, hval]
      · omega
    · omega

theorem sevenHighT0CubeCollectDegreeInputsVal_count_bitAdj
    (edges : BitVec 1176) (vertex : Fin 49)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound
      (orderFortyNineBitAdj edges) acc) :
    let input := sevenHighT0CubeCollectDegreeInputsVal
      (orderFortyNineBitAdj edges) vertex.val acc
    seqPrefixTrue (sevenHighT0CubeInputAccumRow input) input.1.size =
      (Finset.univ.filter fun j =>
        orderFortyNineBitAdj edges vertex j).card := by
  let input := sevenHighT0CubeCollectDegreeInputsVal
    (orderFortyNineBitAdj edges) vertex.val acc
  dsimp only
  rw [sevenHighT0CubeCollectDegreeInputsVal_count_atoms
    (orderFortyNineBitAdj edges) vertex.val acc hacc]
  rw [sevenHighT0CubeIncidentList_eq_otherVertices vertex]
  calc
    ((List.ofFn fun k : Fin 48 =>
        (orderFortyNineOtherVertex vertex k).val).map fun x =>
          sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
            (.edge (min vertex.val x) (max vertex.val x))).count true =
        (List.ofFn (orderFortyNineCounterRow edges vertex)).count true := by
      congr 1
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp only [List.getElem_map, List.getElem_ofFn]
        exact sevenHighT0CubeAtomValue_edge_bitAdj edges vertex
          (orderFortyNineOtherVertex vertex ⟨i, by simpa using hi₁⟩)
    _ = seqPrefixTrue (orderFortyNineCounterRow edges vertex) 48 :=
      (sevenHighT0CubeSeqPrefixTrue_eq_count
        (orderFortyNineCounterRow edges vertex)).symm
    _ = _ := orderFortyNineCounterRow_count edges vertex

def sevenHighT0CubeDegreeStepVal
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
  sevenHighT0CubeEqualsBlockVal input.1
    (sevenHighT0CubeInputAccumRow input)
    (if vertex < 7 then 8 else 7) input.2

theorem sevenHighT0CubeDegreeStepVal_state
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeDegreeStepVal adj vertex acc).1 =
      sevenHighT0CubeDegreeStep vertex acc.1 := by
  let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
  let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
  let raw := incident.foldl (fun input x =>
    let (id, st) := sevenHighT0CubeEdgeId vertex x input.2
    (input.1.push (id : Int), st)) (#[], acc.1)
  have hp : input.1 = raw.1 ∧ input.2.1 = raw.2 :=
    sevenHighT0CubeCollectDegreeInputsVal_projection adj vertex acc
  unfold sevenHighT0CubeDegreeStepVal
  rw [sevenHighT0CubeEqualsBlockVal_state]
  change sevenHighT0CubeEqualsBlock input.1 _ input.2.1 = _
  rw [hp.1, hp.2]
  unfold sevenHighT0CubeDegreeStep
  rfl

theorem sevenHighT0CubeDegreeStepVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (vertex : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hcount : let input :=
        sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
      seqPrefixTrue (sevenHighT0CubeInputAccumRow input) input.1.size =
        if vertex < 7 then 8 else 7) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeDegreeStepVal adj vertex acc) := by
  let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
  have hi := sevenHighT0CubeCollectDegreeInputsVal_sound adj vertex hacc
  unfold sevenHighT0CubeDegreeStepVal
  exact sevenHighT0CubeEqualsBlockVal_semanticSound adj hi.semantic input.1
    (sevenHighT0CubeInputAccumRow input) (if vertex < 7 then 8 else 7)
    (sevenHighT0CubeInputAccum_reifies adj hi) hcount

def sevenHighT0CubeDegreeClausesFromVal
    (adj : Fin 49 → Fin 49 → Bool)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  sevenHighT0CubeVertices.foldl (fun acc vertex =>
    sevenHighT0CubeDegreeStepVal adj vertex acc) acc

theorem sevenHighT0CubeDegreeClausesFromVal_state
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubeDegreeClausesFromVal adj acc).1 =
      sevenHighT0CubeVertices.foldl
        (fun st vertex => sevenHighT0CubeDegreeStep vertex st) acc.1 := by
  unfold sevenHighT0CubeDegreeClausesFromVal
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun vertex acc => sevenHighT0CubeDegreeStepVal_state adj vertex acc)

theorem sevenHighT0CubeDegreeClausesFromVal_generatorState
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState)
    (hstate : acc.1 = sevenHighT0CubeC4Clauses) :
    (sevenHighT0CubeDegreeClausesFromVal adj acc).1 =
      sevenHighT0CubeDegreeClauses := by
  rw [sevenHighT0CubeDegreeClausesFromVal_state, hstate]
  rfl

theorem sevenHighT0CubeDegreeClausesFromVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hcount : ∀ vertex ∈ sevenHighT0CubeVertices,
      ∀ acc : SevenHighT0CubeValState,
      SevenHighT0CubeSemanticSound adj acc →
      let input := sevenHighT0CubeCollectDegreeInputsVal adj vertex acc
      seqPrefixTrue (sevenHighT0CubeInputAccumRow input) input.1.size =
        if vertex < 7 then 8 else 7) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeDegreeClausesFromVal adj acc) := by
  unfold sevenHighT0CubeDegreeClausesFromVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro vertex hv acc hacc
  exact sevenHighT0CubeDegreeStepVal_semanticSound adj vertex hacc
    (hcount vertex hv acc hacc)

theorem sevenHighT0CubeDegreeClausesFromVal_semanticSound_of_degrees
    (edges : BitVec 1176) {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound
      (orderFortyNineBitAdj edges) acc)
    (hdegree : ∀ i : Fin 49,
      (Finset.univ.filter fun j =>
        orderFortyNineBitAdj edges i j).card =
          if i.val < 7 then 8 else 7) :
    SevenHighT0CubeSemanticSound (orderFortyNineBitAdj edges)
      (sevenHighT0CubeDegreeClausesFromVal
        (orderFortyNineBitAdj edges) acc) := by
  apply sevenHighT0CubeDegreeClausesFromVal_semanticSound
    (orderFortyNineBitAdj edges) hacc
  intro vertex hv acc hacc
  have hvlt : vertex < 49 := by
    simpa [sevenHighT0CubeVertices] using hv
  let i : Fin 49 := ⟨vertex, hvlt⟩
  exact (sevenHighT0CubeCollectDegreeInputsVal_count_bitAdj
    edges i acc hacc).trans (hdegree i)

def sevenHighT0CubePartitionCollectStepVal
    (adj : Fin 49 → Fin 49 → Bool) (y x : Nat)
    (input : SevenHighT0CubeCommonAccum) : SevenHighT0CubeCommonAccum :=
  if x = y then input else
    let (id, acc) := sevenHighT0CubeEdgeIdVal adj y x input.2
    (input.1 ++ [(id : Int)], acc)

def sevenHighT0CubePartitionCollectStep (y x : Nat)
    (input : List Int × SevenHighT0CubeGenState) :
    List Int × SevenHighT0CubeGenState :=
  if x = y then input else
    let (id, st) := sevenHighT0CubeEdgeId y x input.2
    (input.1 ++ [(id : Int)], st)

theorem sevenHighT0CubePartitionCollectStepVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (y x : Nat)
    (input : SevenHighT0CubeCommonAccum) :
    let out := sevenHighT0CubePartitionCollectStepVal adj y x input
    (out.1, out.2.1) =
      sevenHighT0CubePartitionCollectStep y x (input.1, input.2.1) := by
  by_cases hxy : x = y
  · simp [sevenHighT0CubePartitionCollectStepVal,
      sevenHighT0CubePartitionCollectStep, hxy]
  · rcases input with ⟨lits, st, val⟩
    simp only [sevenHighT0CubePartitionCollectStepVal,
      sevenHighT0CubePartitionCollectStep, hxy, if_false,
      sevenHighT0CubeEdgeIdVal]
    generalize hv : sevenHighT0CubeAtomIdVal adj
      (.edge (min y x) (max y x)) (st, val) = outVal
    rcases outVal with ⟨idVal, stVal, val'⟩
    generalize hs : sevenHighT0CubeAtomId
      (.edge (min y x) (max y x)) st = out
    rcases out with ⟨id, st'⟩
    have hid := sevenHighT0CubeAtomIdVal_id adj
      (.edge (min y x) (max y x)) st val
    have hstate := sevenHighT0CubeAtomIdVal_state adj
      (.edge (min y x) (max y x)) st val
    rw [hv, hs] at hid hstate
    have hedge : sevenHighT0CubeEdgeId y x st = (id, st') := by
      simpa [sevenHighT0CubeEdgeId] using hs
    rw [hedge]
    have hp : (idVal, stVal) = (id, st') := Prod.ext hid hstate
    exact congrArg (fun p : Nat × SevenHighT0CubeGenState =>
      (lits ++ [(p.1 : Int)], p.2)) hp

theorem sevenHighT0CubePartitionCollectStepVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (y x : Nat)
    {input : SevenHighT0CubeCommonAccum}
    (hinput : SevenHighT0CubeSemanticSound adj input.2) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubePartitionCollectStepVal adj y x input).2 := by
  by_cases hxy : x = y
  · simpa [sevenHighT0CubePartitionCollectStepVal, hxy] using hinput
  · simp only [sevenHighT0CubePartitionCollectStepVal, hxy, if_false,
      sevenHighT0CubeEdgeIdVal]
    exact sevenHighT0CubeAtomIdVal_semanticSound adj hinput _

structure SevenHighT0CubePartitionMatch
    (y : Nat) (xs : List Nat) (input : SevenHighT0CubeCommonAccum) where
  ids : List Nat
  lits_eq : input.1 = List.map (fun id : Nat => (id : Int)) ids
  aligned : List.Forall₂ (fun x id =>
    ((.edge (min y x) (max y x)), id) ∈ input.2.1.ids) xs ids

def sevenHighT0CubePartitionMatch_empty
    (y : Nat) (acc : SevenHighT0CubeValState) :
    SevenHighT0CubePartitionMatch y [] ([], acc) where
  ids := []
  lits_eq := rfl
  aligned := .nil

def sevenHighT0CubePartitionMatch_push
    (adj : Fin 49 → Fin 49 → Bool) {y x : Nat} {xs : List Nat}
    {input : SevenHighT0CubeCommonAccum}
    (h : SevenHighT0CubePartitionMatch y xs input) :
    SevenHighT0CubePartitionMatch y
      (if x = y then xs else xs ++ [x])
      (sevenHighT0CubePartitionCollectStepVal adj y x input) := by
  by_cases hxy : x = y
  · simpa [sevenHighT0CubePartitionCollectStepVal, hxy] using h
  · simp only [hxy, if_false]
    simp only [sevenHighT0CubePartitionCollectStepVal, hxy, if_false,
      sevenHighT0CubeEdgeIdVal]
    generalize hout : sevenHighT0CubeAtomIdVal adj
      (.edge (min y x) (max y x)) input.2 = out
    rcases out with ⟨id, acc'⟩
    refine ⟨h.ids ++ [id], ?_, ?_⟩
    · rw [h.lits_eq]
      simp
    · have hold : List.Forall₂ (fun z oldId =>
          ((.edge (min y z) (max y z)), oldId) ∈ acc'.1.ids) xs h.ids := by
        apply h.aligned.imp
        intro z oldId hm
        have hz := sevenHighT0CubeAtomIdVal_old_mem adj
          (.edge (min y x) (max y x)) input.2.1 input.2.2 hm
        rw [hout] at hz
        exact hz
      have hnew := (sevenHighT0CubeAtomIdVal_result adj
        (.edge (min y x) (max y x)) input.2.1 input.2.2).1
      rw [hout] at hnew
      exact sevenHighT0CubeForall₂_append_singleton hold hnew

def sevenHighT0CubeCollectPartitionVal
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeCommonAccum :=
  (sevenHighT0CubePartitionNeighbors high).foldl (fun input x =>
    sevenHighT0CubePartitionCollectStepVal adj y x input) ([], acc)

theorem sevenHighT0CubePartitionFold_projection
    (adj : Fin 49 → Fin 49 → Bool) (y : Nat) (xs : List Nat)
    (input : SevenHighT0CubeCommonAccum) :
    let outVal := xs.foldl (fun input x =>
      sevenHighT0CubePartitionCollectStepVal adj y x input) input
    let outGen := xs.foldl (fun input x =>
      sevenHighT0CubePartitionCollectStep y x input)
      (input.1, input.2.1)
    (outVal.1, outVal.2.1) = outGen := by
  induction xs generalizing input with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let nextVal := sevenHighT0CubePartitionCollectStepVal adj y x input
      have hstep := sevenHighT0CubePartitionCollectStepVal_projection
        adj y x input
      have hrest := ih nextVal
      change (nextVal.1, nextVal.2.1) =
        sevenHighT0CubePartitionCollectStep y x
          (input.1, input.2.1) at hstep
      rw [hstep] at hrest
      exact hrest

theorem sevenHighT0CubeCollectPartitionVal_projection
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState) :
    let out := sevenHighT0CubeCollectPartitionVal adj y high acc
    (out.1, out.2.1) =
      (sevenHighT0CubePartitionNeighbors high).foldl (fun input x =>
        sevenHighT0CubePartitionCollectStep y x input) ([], acc.1) := by
  simpa only [sevenHighT0CubeCollectPartitionVal] using
    (sevenHighT0CubePartitionFold_projection adj y
      (sevenHighT0CubePartitionNeighbors high) ([], acc))

def sevenHighT0CubeCollectPartitionVal_match
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState) :
    SevenHighT0CubePartitionMatch y
      ((sevenHighT0CubePartitionNeighbors high).filter fun x => x ≠ y)
      (sevenHighT0CubeCollectPartitionVal adj y high acc) := by
  suffices ∀ pre : List Nat,
      SevenHighT0CubePartitionMatch y (pre.filter fun x => x ≠ y)
        (pre.foldl (fun input x =>
          sevenHighT0CubePartitionCollectStepVal adj y x input) ([], acc)) by
    exact this (sevenHighT0CubePartitionNeighbors high)
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact sevenHighT0CubePartitionMatch_empty y acc
  | append_singleton pre x ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.filter_append,
        List.filter_singleton]
      by_cases hxy : x = y
      · simpa [hxy] using
          (sevenHighT0CubePartitionMatch_push adj (y := y) (x := x) ih)
      · simpa [hxy] using
          (sevenHighT0CubePartitionMatch_push adj (y := y) (x := x) ih)

theorem sevenHighT0CubeCollectPartitionVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubeCollectPartitionVal adj y high acc).2 := by
  unfold sevenHighT0CubeCollectPartitionVal
  have hfold : ∀ xs : List Nat, ∀ input : SevenHighT0CubeCommonAccum,
      SevenHighT0CubeSemanticSound adj input.2 →
      SevenHighT0CubeSemanticSound adj
        (xs.foldl (fun input x =>
          sevenHighT0CubePartitionCollectStepVal adj y x input) input).2 := by
    intro xs
    induction xs with
    | nil => exact fun _ h => h
    | cons x xs ih =>
        intro input hinput
        simp only [List.foldl_cons]
        exact ih _ (sevenHighT0CubePartitionCollectStepVal_semanticSound
          adj y x hinput)
  exact hfold _ ([], acc) hacc

theorem sevenHighT0CubeCollectPartitionVal_bounded
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound adj acc) :
    let input := sevenHighT0CubeCollectPartitionVal adj y high acc
    dimacsClauseBounded input.2.1.top input.1 := by
  let input := sevenHighT0CubeCollectPartitionVal adj y high acc
  let hm := sevenHighT0CubeCollectPartitionVal_match adj y high acc
  have hs := sevenHighT0CubeCollectPartitionVal_semanticSound
    adj y high hacc
  change dimacsClauseBounded input.2.1.top input.1
  intro lit hlit
  rw [hm.lits_eq] at hlit
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hlit
  obtain ⟨x, hx, hatom⟩ :=
    sevenHighT0CubeForall₂_exists_left_of_mem hm.aligned hid
  simpa using (hs.ids.id_bounds _ hatom).2

theorem sevenHighT0CubeCollectPartitionVal_positive
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState)
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hwitness : ∃ x ∈ sevenHighT0CubePartitionNeighbors high,
      x ≠ y ∧ sevenHighT0CubeAtomValue adj
        (.edge (min y x) (max y x)) = true) :
    let input := sevenHighT0CubeCollectPartitionVal adj y high acc
    dimacsClauseSatisfied input.2.2 input.1 := by
  let input := sevenHighT0CubeCollectPartitionVal adj y high acc
  let hm := sevenHighT0CubeCollectPartitionVal_match adj y high acc
  have hs := sevenHighT0CubeCollectPartitionVal_semanticSound
    adj y high hacc
  obtain ⟨x, hx, hxy, htrue⟩ := hwitness
  have hxfilter : x ∈
      (sevenHighT0CubePartitionNeighbors high).filter fun z => z ≠ y := by
    simp [hx, hxy]
  obtain ⟨id, hid, hatom⟩ :=
    sevenHighT0CubeForall₂_exists_right_of_mem hm.aligned hxfilter
  have hlit : (id : Int) ∈ input.1 := by
    rw [hm.lits_eq]
    exact List.mem_map.mpr ⟨id, hid, rfl⟩
  have hpos := (hs.ids.id_bounds _ hatom).1
  have hval := (hs.named _ _ hatom).trans htrue
  refine ⟨(id : Int), hlit, ?_⟩
  simp [dimacsLitValue, hpos, hval]

def sevenHighT0CubePartitionClauseVal
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  let input := sevenHighT0CubeCollectPartitionVal adj y high acc
  sevenHighT0CubeEmitVal input.1 input.2

def sevenHighT0CubePartitionClause (y high : Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let input := (sevenHighT0CubePartitionNeighbors high).foldl
    (fun input x => sevenHighT0CubePartitionCollectStep y x input) ([], st)
  sevenHighT0CubeEmit input.1 input.2

set_option maxHeartbeats 1000000 in
theorem sevenHighT0CubePartitionClauseVal_state
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubePartitionClauseVal adj y high acc).1 =
      sevenHighT0CubePartitionClause y high acc.1 := by
  let inputVal := sevenHighT0CubeCollectPartitionVal adj y high acc
  let inputGen := (sevenHighT0CubePartitionNeighbors high).foldl
    (fun input x => sevenHighT0CubePartitionCollectStep y x input) ([], acc.1)
  have hp : (inputVal.1, inputVal.2.1) = inputGen :=
    sevenHighT0CubeCollectPartitionVal_projection adj y high acc
  unfold sevenHighT0CubePartitionClauseVal sevenHighT0CubeEmitVal
  change sevenHighT0CubeEmit inputVal.1 inputVal.2.1 = _
  rw [show inputVal.1 = inputGen.1 from congrArg Prod.fst hp,
    show inputVal.2.1 = inputGen.2 from congrArg Prod.snd hp]
  unfold sevenHighT0CubePartitionClause
  rfl

theorem sevenHighT0CubePartitionClauseVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hpositive : let input :=
        sevenHighT0CubeCollectPartitionVal adj y high acc
      dimacsClauseSatisfied input.2.2 input.1)
    (hbounded : let input :=
        sevenHighT0CubeCollectPartitionVal adj y high acc
      dimacsClauseBounded input.2.1.top input.1) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubePartitionClauseVal adj y high acc) := by
  let input := sevenHighT0CubeCollectPartitionVal adj y high acc
  have hs := sevenHighT0CubeCollectPartitionVal_semanticSound
    adj y high hacc
  exact sevenHighT0CubeEmitVal_semanticSound adj hs input.1
    hpositive hbounded

theorem sevenHighT0CubePartitionClauseVal_semanticSound_of_witness
    (adj : Fin 49 → Fin 49 → Bool) (y high : Nat)
    {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hwitness : ∃ x ∈ sevenHighT0CubePartitionNeighbors high,
      x ≠ y ∧ sevenHighT0CubeAtomValue adj
        (.edge (min y x) (max y x)) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubePartitionClauseVal adj y high acc) := by
  apply sevenHighT0CubePartitionClauseVal_semanticSound adj y high hacc
  · exact sevenHighT0CubeCollectPartitionVal_positive adj y high acc
      hacc hwitness
  · exact sevenHighT0CubeCollectPartitionVal_bounded adj y high acc hacc

def sevenHighT0CubePartitionClausesFromVal
    (adj : Fin 49 → Fin 49 → Bool)
    (acc : SevenHighT0CubeValState) : SevenHighT0CubeValState :=
  sevenHighT0CubeLows.foldl (fun acc y =>
    [0, 1].foldl (fun acc high =>
      sevenHighT0CubePartitionClauseVal adj y high acc) acc) acc

theorem sevenHighT0CubePartitionHighFold_state
    (adj : Fin 49 → Fin 49 → Bool) (y : Nat) (highs : List Nat)
    (acc : SevenHighT0CubeValState) :
    (highs.foldl (fun acc high =>
      sevenHighT0CubePartitionClauseVal adj y high acc) acc).1 =
    highs.foldl (fun st high =>
      sevenHighT0CubePartitionClause y high st) acc.1 := by
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun high acc => sevenHighT0CubePartitionClauseVal_state
      adj y high acc)

theorem sevenHighT0CubePartitionClausesFromVal_state
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState) :
    (sevenHighT0CubePartitionClausesFromVal adj acc).1 =
      sevenHighT0CubeLows.foldl (fun st y =>
        [0, 1].foldl (fun st high =>
          sevenHighT0CubePartitionClause y high st) st) acc.1 := by
  unfold sevenHighT0CubePartitionClausesFromVal
  exact sevenHighT0CubeFoldl_state _ _ _ _
    (fun y acc => sevenHighT0CubePartitionHighFold_state adj y [0, 1] acc)

set_option maxHeartbeats 1000000 in
theorem sevenHighT0CubePartitionClausesFromVal_generatorState
    (adj : Fin 49 → Fin 49 → Bool) (acc : SevenHighT0CubeValState)
    (hstate : acc.1 = sevenHighT0CubeDegreeClauses) :
    (sevenHighT0CubePartitionClausesFromVal adj acc).1 =
      sevenHighT0CubePartitionClauses := by
  rw [sevenHighT0CubePartitionClausesFromVal_state, hstate]
  unfold sevenHighT0CubePartitionClauses sevenHighT0CubePartitionClause
  unfold sevenHighT0CubePartitionCollectStep
  rfl

theorem sevenHighT0CubePartitionClausesFromVal_semanticSound
    (adj : Fin 49 → Fin 49 → Bool) {acc : SevenHighT0CubeValState}
    (hacc : SevenHighT0CubeSemanticSound adj acc)
    (hwitness : ∀ y ∈ sevenHighT0CubeLows, ∀ high ∈ [0, 1],
      ∃ x ∈ sevenHighT0CubePartitionNeighbors high,
        x ≠ y ∧ sevenHighT0CubeAtomValue adj
          (.edge (min y x) (max y x)) = true) :
    SevenHighT0CubeSemanticSound adj
      (sevenHighT0CubePartitionClausesFromVal adj acc) := by
  unfold sevenHighT0CubePartitionClausesFromVal
  apply sevenHighT0CubeSemanticSound_foldl_mem adj _ _ hacc
  intro y hy acc hacc
  apply sevenHighT0CubeSemanticSound_foldl_mem adj [0, 1] _ hacc
  intro high hh acc hacc
  exact sevenHighT0CubePartitionClauseVal_semanticSound_of_witness
    adj y high hacc (hwitness y hy high hh)

structure SevenHighT0CubeRunnerPremises
    (edges : BitVec 1176) (cube : Nat) : Prop where
  independent : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 pair.2) (max pair.1 pair.2)) = false
  n0 : ∀ x ∈ sevenHighT0CubeLows,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges) (.edge 0 x) =
      decide (x < 15)
  matching0 : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN0,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 pair.2) (max pair.1 pair.2)) =
      sevenHighT0CubeMatching0 pair.1 pair.2
  n1seven : sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
    (.edge 1 7) = true
  n1eight : ∀ k ∈ List.range 7,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge 1 (k + 8)) = false
  n1fifteen : ∀ k ∈ List.range 7,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge 1 (k + 15)) = true
  n1twentytwo : ∀ k ∈ List.range 27,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge 1 (k + 22)) = false
  matching1 : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN1,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 pair.2) (max pair.1 pair.2)) =
      sevenHighT0CubeMatching1 pair.1 pair.2
  commonLeft : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
    ∀ w ∈ sevenHighT0CubeLows,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.common pair.1 pair.2 w) = true →
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 w) (max pair.1 w)) = true
  commonRight : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
    ∀ w ∈ sevenHighT0CubeLows,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.common pair.1 pair.2 w) = true →
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.2 w) (max pair.2 w)) = true
  commonWitness : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
    ∃ w ∈ sevenHighT0CubeLows,
      sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
        (.common pair.1 pair.2 w) = true
  c4 : ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeVertices,
    ∀ witnesses ∈ sevenHighT0CubePairs
      (sevenHighT0CubeVertices.filter fun w =>
        w ≠ pair.1 && w ≠ pair.2), ¬(
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 witnesses.1) (max pair.1 witnesses.1)) = true ∧
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.2 witnesses.1) (max pair.2 witnesses.1)) = true ∧
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.1 witnesses.2) (max pair.1 witnesses.2)) = true ∧
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min pair.2 witnesses.2) (max pair.2 witnesses.2)) = true)
  degrees : ∀ i : Fin 49,
    (Finset.univ.filter fun j => orderFortyNineBitAdj edges i j).card =
      if i.val < 7 then 8 else 7
  partition : ∀ y ∈ sevenHighT0CubeLows, ∀ high ∈ [0, 1],
    ∃ x ∈ sevenHighT0CubePartitionNeighbors high,
      x ≠ y ∧ sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
        (.edge (min y x) (max y x)) = true
  cubeUnits : ∀ index ∈ List.range 7,
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge 9 (index + 15)) = decide (index = cube)

def sevenHighT0CubeRunnerN1 (edges : BitVec 1176) :
    SevenHighT0CubeValState :=
  sevenHighT0CubeNormalizeN1Val (orderFortyNineBitAdj edges) (fun _ => false)

def sevenHighT0CubeRunnerCommon (edges : BitVec 1176) :
    SevenHighT0CubeValState :=
  sevenHighT0CubeCommonClausesFromVal (orderFortyNineBitAdj edges)
    (sevenHighT0CubeRunnerN1 edges)

def sevenHighT0CubeRunnerC4 (edges : BitVec 1176) :
    SevenHighT0CubeValState :=
  sevenHighT0CubeC4ClausesFromVal (orderFortyNineBitAdj edges)
    (sevenHighT0CubeRunnerCommon edges)

def sevenHighT0CubeRunnerDegrees (edges : BitVec 1176) :
    SevenHighT0CubeValState :=
  sevenHighT0CubeDegreeClausesFromVal (orderFortyNineBitAdj edges)
    (sevenHighT0CubeRunnerC4 edges)

def sevenHighT0CubeRunnerBeforeFinal (edges : BitVec 1176) :
    SevenHighT0CubeValState :=
  sevenHighT0CubePartitionClausesFromVal (orderFortyNineBitAdj edges)
    (sevenHighT0CubeRunnerDegrees edges)

def sevenHighT0CubeRunner (edges : BitVec 1176) (cube : Nat) :
    SevenHighT0CubeValState :=
  sevenHighT0CubeFinalUnitsVal (orderFortyNineBitAdj edges) cube
    (sevenHighT0CubeRunnerBeforeFinal edges)

set_option maxHeartbeats 1000000 in
theorem sevenHighT0CubeRunner_semanticSound
    (edges : BitVec 1176) (cube : Nat)
    (h : SevenHighT0CubeRunnerPremises edges cube) :
    SevenHighT0CubeSemanticSound (orderFortyNineBitAdj edges)
      (sevenHighT0CubeRunner edges cube) := by
  let adj := orderFortyNineBitAdj edges
  let initial : DimacsValuation := fun _ => false
  let n0 := sevenHighT0CubeNormalizeN0Val adj initial
  let n1 := sevenHighT0CubeNormalizeN1Val adj initial
  let common := sevenHighT0CubeCommonClausesFromVal adj n1
  let c4 := sevenHighT0CubeC4ClausesFromVal adj common
  let degrees := sevenHighT0CubeDegreeClausesFromVal adj c4
  let partition := sevenHighT0CubePartitionClausesFromVal adj degrees
  have hs0 := sevenHighT0CubeNormalizeN0Val_semanticSound adj initial
    h.independent h.n0 h.matching0
  have hs1 := sevenHighT0CubeNormalizeN1Val_semanticSound adj initial hs0
    h.n1seven h.n1eight h.n1fifteen h.n1twentytwo h.matching1
  have hsCommon := sevenHighT0CubeCommonClausesFromVal_semanticSound
    adj hs1 h.commonLeft h.commonRight h.commonWitness
  have hsC4 := sevenHighT0CubeC4ClausesFromVal_semanticSound
    adj hsCommon h.c4
  have hsDegrees :=
    sevenHighT0CubeDegreeClausesFromVal_semanticSound_of_degrees
      edges hsC4 h.degrees
  have hsPartition := sevenHighT0CubePartitionClausesFromVal_semanticSound
    adj hsDegrees h.partition
  exact sevenHighT0CubeFinalUnitsVal_semanticSound adj cube
    hsPartition h.cubeUnits

/-- Projection of the runner soundness theorem used by downstream DIMACS
bridges.  Keeping the projection next to the construction prevents clients
from re-elaborating the enormous generated runner state merely to select its
`satisfied` field. -/
theorem sevenHighT0CubeRunner_formulaSatisfied
    (edges : BitVec 1176) (cube : Nat)
    (h : SevenHighT0CubeRunnerPremises edges cube) :
    dimacsFormulaSatisfied (sevenHighT0CubeRunner edges cube).2
      (sevenHighT0CubeRunner edges cube).1.clauses :=
  (sevenHighT0CubeRunner_semanticSound edges cube h).satisfied

theorem sevenHighT0CubeRunnerN1_state (edges : BitVec 1176) :
    (sevenHighT0CubeRunnerN1 edges).1 = sevenHighT0CubeNormalizeN1 := by
  exact sevenHighT0CubeNormalizeN1Val_state
    (orderFortyNineBitAdj edges) (fun _ => false)

theorem sevenHighT0CubeRunnerCommon_state (edges : BitVec 1176) :
    (sevenHighT0CubeRunnerCommon edges).1 = sevenHighT0CubeCommonClauses := by
  exact sevenHighT0CubeCommonClausesFromVal_generatorState
    (orderFortyNineBitAdj edges) (sevenHighT0CubeRunnerN1 edges)
    (sevenHighT0CubeRunnerN1_state edges)

theorem sevenHighT0CubeRunnerC4_state (edges : BitVec 1176) :
    (sevenHighT0CubeRunnerC4 edges).1 = sevenHighT0CubeC4Clauses := by
  exact sevenHighT0CubeC4ClausesFromVal_generatorState
    (orderFortyNineBitAdj edges) (sevenHighT0CubeRunnerCommon edges)
    (sevenHighT0CubeRunnerCommon_state edges)

theorem sevenHighT0CubeRunnerDegrees_state (edges : BitVec 1176) :
    (sevenHighT0CubeRunnerDegrees edges).1 = sevenHighT0CubeDegreeClauses := by
  exact sevenHighT0CubeDegreeClausesFromVal_generatorState
    (orderFortyNineBitAdj edges) (sevenHighT0CubeRunnerC4 edges)
    (sevenHighT0CubeRunnerC4_state edges)

theorem sevenHighT0CubeRunnerBeforeFinal_state (edges : BitVec 1176) :
    (sevenHighT0CubeRunnerBeforeFinal edges).1 =
      sevenHighT0CubePartitionClauses := by
  exact sevenHighT0CubePartitionClausesFromVal_generatorState
    (orderFortyNineBitAdj edges) (sevenHighT0CubeRunnerDegrees edges)
    (sevenHighT0CubeRunnerDegrees_state edges)

theorem sevenHighT0CubeRunner_state
    (edges : BitVec 1176) (cube : Nat) :
    (sevenHighT0CubeRunner edges cube).1 =
      sevenHighT0CubeFinalState cube := by
  exact sevenHighT0CubeFinalUnitsVal_finalState
    (orderFortyNineBitAdj edges) cube
    (sevenHighT0CubeRunnerBeforeFinal edges)
    (sevenHighT0CubeRunnerBeforeFinal_state edges)

/-- The runner valuation satisfies the exact final-state DIMACS formula. -/
theorem sevenHighT0CubeRunner_finalFormulaSatisfied
    (edges : BitVec 1176) (cube : Nat)
    (h : SevenHighT0CubeRunnerPremises edges cube) :
    dimacsFormulaSatisfied (sevenHighT0CubeRunner edges cube).2
      (sevenHighT0CubeFinalState cube).clauses := by
  rw [← sevenHighT0CubeRunner_state edges cube]
  exact sevenHighT0CubeRunner_formulaSatisfied edges cube h

end Erdos85
