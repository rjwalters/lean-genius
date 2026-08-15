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

end Erdos85
