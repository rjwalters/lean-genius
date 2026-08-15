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

end Erdos85
