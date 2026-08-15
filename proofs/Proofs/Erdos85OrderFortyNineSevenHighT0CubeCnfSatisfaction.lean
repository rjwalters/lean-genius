import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf
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

end Erdos85
