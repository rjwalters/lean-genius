import Proofs.Erdos85SequentialCounterGenerator
import Proofs.Erdos85OneHighFamilyCnfSemantics

/-!
# Exact one-high family CNF generator

This is a functional Lean transcription of the named-atom `IDPool` and the
ordered clause loops in `family_gen.py`.  Cardinality blocks delegate to the
already verified exact PySAT sequential-counter generator.
-/

namespace Erdos85

inductive OneHighFamilyAtom where
  | edge : Nat → Nat → OneHighFamilyAtom
  | miss : Nat → Nat → OneHighFamilyAtom
  | midpoint : Nat → Nat → Nat → OneHighFamilyAtom
  | common : Nat → Nat → OneHighFamilyAtom
deriving DecidableEq, Repr

structure OneHighFamilyGenState where
  top : Nat := 0
  ids : List (OneHighFamilyAtom × Nat) := []
  clauses : Array DimacsClause := #[]
deriving Repr, DecidableEq

/-- Integrity of the named `IDPool` table.  Counter auxiliaries may create
holes between named IDs, so only positivity and the global-top bound are
required in addition to injectivity in both directions. -/
structure OneHighFamilyIdsSound (st : OneHighFamilyGenState) : Prop where
  keys_nodup : (st.ids.map Prod.fst).Nodup
  ids_nodup : (st.ids.map Prod.snd).Nodup
  id_bounds : ∀ entry ∈ st.ids, 0 < entry.2 ∧ entry.2 ≤ st.top

def oneHighFamilyLookup (atom : OneHighFamilyAtom) :
    List (OneHighFamilyAtom × Nat) → Option Nat
  | [] => none
  | entry :: rest =>
      if entry.1 = atom then some entry.2 else oneHighFamilyLookup atom rest

theorem oneHighFamilyLookup_eq_none_iff
    (atom : OneHighFamilyAtom) (ids : List (OneHighFamilyAtom × Nat)) :
    oneHighFamilyLookup atom ids = none ↔ atom ∉ ids.map Prod.fst := by
  induction ids with
  | nil => simp [oneHighFamilyLookup]
  | cons entry rest ih =>
      simp only [oneHighFamilyLookup, List.map_cons, List.mem_cons]
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

theorem oneHighFamilyLookup_eq_some_mem
    {atom : OneHighFamilyAtom} {id : Nat}
    {ids : List (OneHighFamilyAtom × Nat)}
    (h : oneHighFamilyLookup atom ids = some id) :
    (atom, id) ∈ ids := by
  induction ids with
  | nil => simp [oneHighFamilyLookup] at h
  | cons entry rest ih =>
      rw [List.mem_cons]
      rw [oneHighFamilyLookup] at h
      split at h
      next heq =>
        simp only [Option.some.injEq] at h
        subst id
        exact Or.inl (Prod.ext heq.symm rfl)
      next => exact Or.inr (ih h)

/-- PySAT `IDPool.id`: named atoms are memoized, while the next fresh ID is
strictly above the current global top (including prior counter auxiliaries). -/
def oneHighFamilyAtomId (atom : OneHighFamilyAtom) :
    StateM OneHighFamilyGenState Nat := fun st =>
  match oneHighFamilyLookup atom st.ids with
  | some id => (id, st)
  | none =>
      let id := st.top + 1
      (id, { st with top := id, ids := (atom, id) :: st.ids })

theorem oneHighFamilyIdsSound_initial :
    OneHighFamilyIdsSound ({} : OneHighFamilyGenState) := by
  constructor <;> simp

theorem oneHighFamilyIdsSound_atomId
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (atom : OneHighFamilyAtom) :
    OneHighFamilyIdsSound (oneHighFamilyAtomId atom st).2 := by
  unfold oneHighFamilyAtomId
  split
  next id hlookup => simpa using h
  next hlookup =>
    constructor
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨(oneHighFamilyLookup_eq_none_iff atom st.ids).mp hlookup,
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

theorem oneHighFamilyAtomId_mem (atom : OneHighFamilyAtom)
    (st : OneHighFamilyGenState) :
    (atom, (oneHighFamilyAtomId atom st).1) ∈
      (oneHighFamilyAtomId atom st).2.ids := by
  unfold oneHighFamilyAtomId
  split
  next id hlookup =>
    exact oneHighFamilyLookup_eq_some_mem hlookup
  next hlookup => simp

theorem oneHighFamilyAtomId_ids_subset (atom : OneHighFamilyAtom)
    (st : OneHighFamilyGenState) :
    ∀ entry ∈ st.ids, entry ∈ (oneHighFamilyAtomId atom st).2.ids := by
  unfold oneHighFamilyAtomId
  split
  · exact fun entry hentry => hentry
  · intro entry hentry
    exact List.mem_cons_of_mem _ hentry

def oneHighFamilyEdgeId (i j : Nat) : StateM OneHighFamilyGenState Nat :=
  oneHighFamilyAtomId (.edge (min i j) (max i j))

def oneHighFamilyEmit (clause : DimacsClause) :
    StateM OneHighFamilyGenState Unit :=
  modify fun st => { st with clauses := st.clauses.push clause }

theorem oneHighFamilyIdsSound_emit
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (clause : DimacsClause) :
    OneHighFamilyIdsSound (oneHighFamilyEmit clause st).2 := by
  change OneHighFamilyIdsSound { st with clauses := st.clauses.push clause }
  constructor
  · exact h.keys_nodup
  · exact h.ids_nodup
  · exact h.id_bounds

def oneHighFamilyRunList {α : Type} (xs : List α)
    (step : α → OneHighFamilyGenState → OneHighFamilyGenState)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  xs.foldl (fun st x => step x st) st

theorem oneHighFamilyIdsSound_runList {α : Type} (xs : List α)
    (step : α → OneHighFamilyGenState → OneHighFamilyGenState)
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (hstep : ∀ x st, OneHighFamilyIdsSound st →
      OneHighFamilyIdsSound (step x st)) :
    OneHighFamilyIdsSound (oneHighFamilyRunList xs step st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih =>
      simp only [oneHighFamilyRunList, List.foldl_cons]
      exact ih (hstep x st h)

theorem oneHighFamilyIdsSound_foldlAccum {α β : Type} (xs : List α)
    (step : α → (β × OneHighFamilyGenState) →
      β × OneHighFamilyGenState)
    (acc : β) {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (hstep : ∀ x acc st, OneHighFamilyIdsSound st →
      OneHighFamilyIdsSound (step x (acc, st)).2) :
    OneHighFamilyIdsSound (xs.foldl (fun accst x => step x accst) (acc, st)).2 := by
  induction xs generalizing acc st with
  | nil => exact h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      generalize heq : step x (acc, st) = out
      rcases out with ⟨acc', st'⟩
      have hx := hstep x acc st h
      rw [heq] at hx
      exact ih acc' hx

theorem oneHighFamilyIdsSound_arrayFoldl {α : Type} (xs : Array α)
    (step : OneHighFamilyGenState → α → OneHighFamilyGenState)
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (hstep : ∀ st x, OneHighFamilyIdsSound st →
      OneHighFamilyIdsSound (step st x)) :
    OneHighFamilyIdsSound (xs.foldl step st) := by
  rw [← Array.foldl_toList]
  exact oneHighFamilyIdsSound_runList xs.toList (fun x st => step st x) h
    (fun x st hs => hstep st x hs)

theorem oneHighFamilyIdsSound_edgeId
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (i j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyEdgeId i j st).2 := by
  exact oneHighFamilyIdsSound_atomId h _

def oneHighFamilyInternalPairStep (a b i j : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (id, st) := oneHighFamilyEdgeId (5 * b + i) (5 * b + j) st
  let twoEdges := ¬(b % 2 = 0 ∧ b / 2 < a)
  let present := (i = 0 ∧ j = 1) ∨ (twoEdges ∧ i = 2 ∧ j = 3)
  (oneHighFamilyEmit [if present then (id : Int) else -(id : Int)] st).2

theorem oneHighFamilyIdsSound_internalPairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a b i j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyInternalPairStep a b i j st) := by
  simp only [oneHighFamilyInternalPairStep]
  generalize heq : oneHighFamilyEdgeId (5 * b + i) (5 * b + j) st = out
  rcases out with ⟨id, st'⟩
  have hs := oneHighFamilyIdsSound_edgeId h (5 * b + i) (5 * b + j)
  rw [heq] at hs
  exact oneHighFamilyIdsSound_emit hs _

def oneHighFamilyInternalBlockStep (a b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 5) (fun i st =>
    oneHighFamilyRunList (List.range 5) (fun j st =>
      if i < j then oneHighFamilyInternalPairStep a b i j st else st) st) st

theorem oneHighFamilyIdsSound_internalBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a b : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyInternalBlockStep a b st) := by
  apply oneHighFamilyIdsSound_runList _ _ h
  intro i st hi
  apply oneHighFamilyIdsSound_runList _ _ hi
  intro j st hj
  split
  · exact oneHighFamilyIdsSound_internalPairStep hj a b i j
  · exact hj

/-- First generator segment: the 80 within-block matching unit clauses. -/
def oneHighFamilyInternalUnits (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) (oneHighFamilyInternalBlockStep a) {}

theorem oneHighFamilyIdsSound_internalUnits (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyInternalUnits a) := by
  exact oneHighFamilyIdsSound_runList _ _ oneHighFamilyIdsSound_initial
    (fun b st h => oneHighFamilyIdsSound_internalBlockStep h a b)

def oneHighFamilyMatePairStep (b i j : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (id, st) := oneHighFamilyEdgeId (5 * b + i) (5 * (b + 1) + j) st
  (oneHighFamilyEmit [-(id : Int)] st).2

theorem oneHighFamilyIdsSound_matePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (b i j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMatePairStep b i j st) := by
  simp only [oneHighFamilyMatePairStep]
  generalize heq : oneHighFamilyEdgeId (5 * b + i) (5 * (b + 1) + j) st = out
  rcases out with ⟨id, st'⟩
  have hs := oneHighFamilyIdsSound_edgeId h (5 * b + i) (5 * (b + 1) + j)
  rw [heq] at hs
  exact oneHighFamilyIdsSound_emit hs _

def oneHighFamilyMateBlockStep (b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 5) (fun i st =>
    oneHighFamilyRunList (List.range 5)
      (fun j st => oneHighFamilyMatePairStep b i j st) st) st

theorem oneHighFamilyIdsSound_mateBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (b : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMateBlockStep b st) := by
  apply oneHighFamilyIdsSound_runList _ _ h
  intro i st hi
  exact oneHighFamilyIdsSound_runList _ _ hi
    (fun j st hj => oneHighFamilyIdsSound_matePairStep hj b i j)

/-- Second generator segment: the 100 zero units between standard-mate
blocks, starting from the completed internal-unit state. -/
def oneHighFamilyBaseUnits (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList [0, 2, 4, 6] oneHighFamilyMateBlockStep
    (oneHighFamilyInternalUnits a)

theorem oneHighFamilyIdsSound_baseUnits (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyBaseUnits a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_internalUnits a)
    (fun b st h => oneHighFamilyIdsSound_mateBlockStep h b)

def oneHighFamilyC4SameMidpointStep (i j w : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (eiw, st) := oneHighFamilyEdgeId i w st
  let (ejw, st) := oneHighFamilyEdgeId j w st
  (oneHighFamilyEmit [-(eiw : Int), -(ejw : Int)] st).2

theorem oneHighFamilyIdsSound_c4SameMidpointStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (i j w : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyC4SameMidpointStep i j w st) := by
  simp only [oneHighFamilyC4SameMidpointStep]
  generalize h₁ : oneHighFamilyEdgeId i w st = out₁
  rcases out₁ with ⟨eiw, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_edgeId h i w
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyEdgeId j w st₁ = out₂
  rcases out₂ with ⟨ejw, st₂⟩
  have hs₂ := oneHighFamilyIdsSound_edgeId hs₁ j w
  rw [h₂] at hs₂
  simp only [h₂]
  exact oneHighFamilyIdsSound_emit hs₂ _

def oneHighFamilyC4CrossMidpointsStep (i j w w' : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (eiw, st) := oneHighFamilyEdgeId i w st
  let (ejw, st) := oneHighFamilyEdgeId j w st
  let (eiw', st) := oneHighFamilyEdgeId i w' st
  let (ejw', st) := oneHighFamilyEdgeId j w' st
  (oneHighFamilyEmit
    [-(eiw : Int), -(ejw : Int), -(eiw' : Int), -(ejw' : Int)] st).2

theorem oneHighFamilyIdsSound_c4CrossMidpointsStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (i j w w' : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyC4CrossMidpointsStep i j w w' st) := by
  simp only [oneHighFamilyC4CrossMidpointsStep]
  generalize h₁ : oneHighFamilyEdgeId i w st = out₁
  rcases out₁ with ⟨eiw, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_edgeId h i w
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyEdgeId j w st₁ = out₂
  rcases out₂ with ⟨ejw, st₂⟩
  have hs₂ := oneHighFamilyIdsSound_edgeId hs₁ j w
  rw [h₂] at hs₂
  generalize h₃ : oneHighFamilyEdgeId i w' st₂ = out₃
  rcases out₃ with ⟨eiw', st₃⟩
  have hs₃ := oneHighFamilyIdsSound_edgeId hs₂ i w'
  rw [h₃] at hs₃
  generalize h₄ : oneHighFamilyEdgeId j w' st₃ = out₄
  rcases out₄ with ⟨ejw', st₄⟩
  have hs₄ := oneHighFamilyIdsSound_edgeId hs₃ j w'
  rw [h₄] at hs₄
  simp only [h₂, h₃, h₄]
  exact oneHighFamilyIdsSound_emit hs₄ _

def oneHighFamilyOtherVertices (i j : Nat) : List Nat :=
  (List.range 40).filter fun w => w ≠ i ∧ w ≠ j

def oneHighFamilyC4PairStep (i j : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let others := oneHighFamilyOtherVertices i j
  if i / 5 = j / 5 then
    oneHighFamilyRunList others
      (fun w st => oneHighFamilyC4SameMidpointStep i j w st) st
  else
    oneHighFamilyRunList others (fun w st =>
      oneHighFamilyRunList others (fun w' st =>
        if w < w' then oneHighFamilyC4CrossMidpointsStep i j w w' st else st)
        st) st

theorem oneHighFamilyIdsSound_c4PairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (i j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyC4PairStep i j st) := by
  simp only [oneHighFamilyC4PairStep]
  split
  · exact oneHighFamilyIdsSound_runList _ _ h
      (fun w st hw => oneHighFamilyIdsSound_c4SameMidpointStep hw i j w)
  · apply oneHighFamilyIdsSound_runList _ _ h
    intro w st hw
    apply oneHighFamilyIdsSound_runList _ _ hw
    intro w' st hw'
    split
    · exact oneHighFamilyIdsSound_c4CrossMidpointsStep hw' i j w w'
    · exact hw'

def oneHighFamilyC4OuterStep (i : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) (fun j st =>
    if i < j then oneHighFamilyC4PairStep i j st else st) st

theorem oneHighFamilyIdsSound_c4OuterStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (i : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyC4OuterStep i st) := by
  apply oneHighFamilyIdsSound_runList _ _ h
  intro j st hj
  split
  · exact oneHighFamilyIdsSound_c4PairStep hj i j
  · exact hj

/-- Third generator segment: same-block zero-common-neighbor clauses and
general cross-block at-most-one-common-neighbor clauses, in the exact nested
`itertools.combinations` order. -/
def oneHighFamilyC4Clauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) oneHighFamilyC4OuterStep
    (oneHighFamilyBaseUnits a)

theorem oneHighFamilyIdsSound_c4Clauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyC4Clauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_baseUnits a)
    (fun i st h => oneHighFamilyIdsSound_c4OuterStep h i)

def oneHighFamilyBlockVertices (b : Nat) : List Nat :=
  (List.range 5).map fun r => 5 * b + r

def oneHighFamilyAtMostOnePairStep (y x x' : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (eyx, st) := oneHighFamilyEdgeId y x st
  let (eyx', st) := oneHighFamilyEdgeId y x' st
  (oneHighFamilyEmit [-(eyx : Int), -(eyx' : Int)] st).2

theorem oneHighFamilyIdsSound_atMostOnePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (y x x' : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyAtMostOnePairStep y x x' st) := by
  simp only [oneHighFamilyAtMostOnePairStep]
  generalize h₁ : oneHighFamilyEdgeId y x st = out₁
  rcases out₁ with ⟨eyx, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_edgeId h y x
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyEdgeId y x' st₁ = out₂
  rcases out₂ with ⟨eyx', st₂⟩
  have hs₂ := oneHighFamilyIdsSound_edgeId hs₁ y x'
  rw [h₂] at hs₂
  simp only [h₂]
  exact oneHighFamilyIdsSound_emit hs₂ _

def oneHighFamilyAtMostOneVertexStep (b y : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  if y / 5 = b ^^^ 1 then st else
    let xs := (oneHighFamilyBlockVertices b).filter fun x => x ≠ y
    oneHighFamilyRunList xs (fun x st =>
      oneHighFamilyRunList xs (fun x' st =>
        if x < x' then oneHighFamilyAtMostOnePairStep y x x' st else st) st) st

theorem oneHighFamilyIdsSound_atMostOneVertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (b y : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyAtMostOneVertexStep b y st) := by
  simp only [oneHighFamilyAtMostOneVertexStep]
  split
  · exact h
  · apply oneHighFamilyIdsSound_runList _ _ h
    intro x st hx
    apply oneHighFamilyIdsSound_runList _ _ hx
    intro x' st hx'
    split
    · exact oneHighFamilyIdsSound_atMostOnePairStep hx' y x x'
    · exact hx'

def oneHighFamilyAtMostOneBlockStep (b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40)
    (oneHighFamilyAtMostOneVertexStep b) st

theorem oneHighFamilyIdsSound_atMostOneBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (b : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyAtMostOneBlockStep b st) := by
  exact oneHighFamilyIdsSound_runList _ _ h
    (fun y st hy => oneHighFamilyIdsSound_atMostOneVertexStep hy b y)

/-- Fourth generator segment: every vertex has at most one neighbor in a
non-mate block. -/
def oneHighFamilyAtMostOneBlockClauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) oneHighFamilyAtMostOneBlockStep
    (oneHighFamilyC4Clauses a)

theorem oneHighFamilyIdsSound_atMostOneBlockClauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyAtMostOneBlockClauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_c4Clauses a)
    (fun b st h => oneHighFamilyIdsSound_atMostOneBlockStep h b)

def oneHighFamilyFarVertices (y : Nat) : List Nat :=
  (List.range 40).filter fun x =>
    x ≠ y ∧ x / 5 ≠ y / 5 ∧ x / 5 ≠ (y / 5 ^^^ 1)

def oneHighFamilyFarDegreeBound (a y : Nat) : Nat :=
  let b := y / 5
  let r := y % 5
  let internalEdges := if b % 2 = 0 ∧ b / 2 < a then 1 else 2
  if r < 2 ∨ (internalEdges = 2 ∧ r < 4) then 5 else 6

/-- Incorporate a `CardEnc.equals` block into the named-atom generator state.
Counter auxiliaries advance the global top but do not enter `IDPool.obj2id`. -/
def oneHighFamilyEqualsBlock (vars : Array Int) (bound : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let out := seqCounterEquals st.top vars bound
  { st with top := out.top, clauses := st.clauses ++ out.clauses }

theorem oneHighFamilyIdsSound_equalsBlock
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (vars : Array Int) (bound : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyEqualsBlock vars bound st) := by
  constructor
  · exact h.keys_nodup
  · exact h.ids_nodup
  · intro entry hentry
    have hb := h.id_bounds entry hentry
    exact ⟨hb.1, hb.2.trans (by
      simpa [oneHighFamilyEqualsBlock] using
        seqCounterEquals_top_bound st.top vars bound)⟩

def oneHighFamilyFarDegreeStep (a y : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (vars, st) := (oneHighFamilyFarVertices y).foldl (fun (acc, st) x =>
    let (id, st) := oneHighFamilyEdgeId y x st
    (acc.push (id : Int), st)) (#[], st)
  oneHighFamilyEqualsBlock vars (oneHighFamilyFarDegreeBound a y) st

theorem oneHighFamilyIdsSound_farDegreeStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a y : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyFarDegreeStep a y st) := by
  simp only [oneHighFamilyFarDegreeStep]
  generalize heq : (oneHighFamilyFarVertices y).foldl (fun (acc, st) x =>
    let (id, st) := oneHighFamilyEdgeId y x st
    (acc.push (id : Int), st)) (#[], st) = out
  rcases out with ⟨vars, st'⟩
  apply oneHighFamilyIdsSound_equalsBlock _ vars _
  have hs := oneHighFamilyIdsSound_foldlAccum (oneHighFamilyFarVertices y)
    (fun x (accst : Array Int × OneHighFamilyGenState) =>
      let (acc, st) := accst
      let (id, st) := oneHighFamilyEdgeId y x st
      (acc.push (id : Int), st)) #[] h (by
        intro x acc st hx
        exact oneHighFamilyIdsSound_edgeId hx y x)
  rw [heq] at hs
  exact hs

/-- Fifth generator segment: forty exact far-degree equality counters. -/
def oneHighFamilyFarDegreeClauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) (oneHighFamilyFarDegreeStep a)
    (oneHighFamilyAtMostOneBlockClauses a)

theorem oneHighFamilyIdsSound_farDegreeClauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyFarDegreeClauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_atMostOneBlockClauses a)
    (fun y st h => oneHighFamilyIdsSound_farDegreeStep h a y)

def oneHighFamilyVertexMatched (a w : Nat) : Bool :=
  let b := w / 5
  let r := w % 5
  decide (r < 2 ∨ (¬(b % 2 = 0 ∧ b / 2 < a) ∧ r < 4))

def oneHighFamilyMissDefinitionStep (w b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  if b = w / 5 ∨ b = (w / 5 ^^^ 1) then st else
    let (xv, st) := oneHighFamilyAtomId (.miss w b) st
    let (lits, st) := (oneHighFamilyBlockVertices b).foldl
      (fun (acc, st) z =>
        let (id, st) := oneHighFamilyEdgeId w z st
        (acc.push (id : Int), st)) (#[], st)
    let st := lits.foldl
      (fun st lit => (oneHighFamilyEmit [-(xv : Int), -lit] st).2) st
    (oneHighFamilyEmit ((xv : Int) :: lits.toList) st).2

theorem oneHighFamilyIdsSound_missDefinitionStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (w b : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMissDefinitionStep w b st) := by
  simp only [oneHighFamilyMissDefinitionStep]
  split
  · exact h
  · generalize h₁ : oneHighFamilyAtomId (.miss w b) st = out₁
    rcases out₁ with ⟨xv, st₁⟩
    have hs₁ := oneHighFamilyIdsSound_atomId h (.miss w b)
    rw [h₁] at hs₁
    generalize h₂ : (oneHighFamilyBlockVertices b).foldl
      (fun (acc, st) z =>
        let (id, st) := oneHighFamilyEdgeId w z st
        (acc.push (id : Int), st)) (#[], st₁) = out₂
    rcases out₂ with ⟨lits, st₂⟩
    have hs₂ := oneHighFamilyIdsSound_foldlAccum
      (oneHighFamilyBlockVertices b)
      (fun z (accst : Array Int × OneHighFamilyGenState) =>
        let (acc, st) := accst
        let (id, st) := oneHighFamilyEdgeId w z st
        (acc.push (id : Int), st)) #[] hs₁ (by
          intro z acc st hz
          exact oneHighFamilyIdsSound_edgeId hz w z)
    rw [h₂] at hs₂
    have hs₃ := oneHighFamilyIdsSound_arrayFoldl lits
      (fun st lit => (oneHighFamilyEmit [-(xv : Int), -lit] st).2)
      hs₂ (by
        intro st lit hs
        exact oneHighFamilyIdsSound_emit hs _)
    simp only [h₂]
    exact oneHighFamilyIdsSound_emit hs₃ _

def oneHighFamilyMissVertexStep (a w : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  if oneHighFamilyVertexMatched a w then
    oneHighFamilyRunList (List.range 8)
      (oneHighFamilyMissDefinitionStep w) st
  else st

theorem oneHighFamilyIdsSound_missVertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a w : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMissVertexStep a w st) := by
  simp only [oneHighFamilyMissVertexStep]
  split
  · exact oneHighFamilyIdsSound_runList _ _ h
      (fun b st hb => oneHighFamilyIdsSound_missDefinitionStep hb w b)
  · exact h

/-- Sixth generator segment: exact Tseitin definitions of every matched
leaf's six missing-block variables. -/
def oneHighFamilyMissDefinitionClauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) (oneHighFamilyMissVertexStep a)
    (oneHighFamilyFarDegreeClauses a)

theorem oneHighFamilyIdsSound_missDefinitionClauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMissDefinitionClauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_farDegreeClauses a)
    (fun w st h => oneHighFamilyIdsSound_missVertexStep h a w)

def oneHighFamilyFarBlocks (c : Nat) : List Nat :=
  (List.range 8).filter fun b => b ≠ c ∧ b ≠ (c ^^^ 1)

def oneHighFamilyLexPairStep (x y j k : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  if j > k then
    let (xj, st) := oneHighFamilyAtomId (.miss x j) st
    let (yk, st) := oneHighFamilyAtomId (.miss y k) st
    (oneHighFamilyEmit [-(xj : Int), -(yk : Int)] st).2
  else st

theorem oneHighFamilyIdsSound_lexPairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (x y j k : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyLexPairStep x y j k st) := by
  simp only [oneHighFamilyLexPairStep]
  split
  · generalize h₁ : oneHighFamilyAtomId (.miss x j) st = out₁
    rcases out₁ with ⟨xj, st₁⟩
    have hs₁ := oneHighFamilyIdsSound_atomId h (.miss x j)
    rw [h₁] at hs₁
    generalize h₂ : oneHighFamilyAtomId (.miss y k) st₁ = out₂
    rcases out₂ with ⟨yk, st₂⟩
    have hs₂ := oneHighFamilyIdsSound_atomId hs₁ (.miss y k)
    rw [h₂] at hs₂
    simp only [h₂]
    exact oneHighFamilyIdsSound_emit hs₂ _
  · exact h

def oneHighFamilyLexLeq (c x y : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let fars := oneHighFamilyFarBlocks c
  oneHighFamilyRunList fars (fun j st =>
    oneHighFamilyRunList fars
      (fun k st => oneHighFamilyLexPairStep x y j k st) st) st

theorem oneHighFamilyIdsSound_lexLeq
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (c x y : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyLexLeq c x y st) := by
  apply oneHighFamilyIdsSound_runList _ _ h
  intro j st hj
  exact oneHighFamilyIdsSound_runList _ _ hj
    (fun k st hk => oneHighFamilyIdsSound_lexPairStep hk x y j k)

def oneHighFamilyLexBlockStep (a c : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let base := 5 * c
  let st := oneHighFamilyLexLeq c base (base + 1) st
  if ¬(c % 2 = 0 ∧ c / 2 < a) then
    let st := oneHighFamilyLexLeq c (base + 2) (base + 3) st
    oneHighFamilyLexLeq c base (base + 2) st
  else st

theorem oneHighFamilyIdsSound_lexBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a c : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyLexBlockStep a c st) := by
  simp only [oneHighFamilyLexBlockStep]
  have hbase := oneHighFamilyIdsSound_lexLeq h c (5 * c) (5 * c + 1)
  split
  · exact oneHighFamilyIdsSound_lexLeq
      (oneHighFamilyIdsSound_lexLeq hbase c (5 * c + 2) (5 * c + 3))
      c (5 * c) (5 * c + 2)
  · exact hbase

/-- Seventh generator segment: the three matched-pair lex WLOG families. -/
def oneHighFamilyLexClauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) (oneHighFamilyLexBlockStep a)
    (oneHighFamilyMissDefinitionClauses a)

theorem oneHighFamilyIdsSound_lexClauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyLexClauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_missDefinitionClauses a)
    (fun c st h => oneHighFamilyIdsSound_lexBlockStep h a c)

def oneHighFamilyMidpointAtomId (x w z : Nat) :
    StateM OneHighFamilyGenState Nat :=
  oneHighFamilyAtomId (.midpoint (min x z) w (max x z))

theorem oneHighFamilyIdsSound_midpointAtomId
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (x w z : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyMidpointAtomId x w z st).2 := by
  exact oneHighFamilyIdsSound_atomId h _

def oneHighFamilyCommonAtomId (x z : Nat) :
    StateM OneHighFamilyGenState Nat :=
  oneHighFamilyAtomId (.common (min x z) (max x z))

theorem oneHighFamilyIdsSound_commonAtomId
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (x z : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyCommonAtomId x z st).2 := by
  exact oneHighFamilyIdsSound_atomId h _

def oneHighFamilyPairedMidpoints (bi bj : Nat) : List Nat :=
  (List.range 40).filter fun w => w / 5 ≠ bi ∧ w / 5 ≠ bj

def oneHighFamilyMidpointTseitinStep (x z w : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (ts, st) := accst
  let (t, st) := oneHighFamilyMidpointAtomId x w z st
  let (exw, st) := oneHighFamilyEdgeId x w st
  let (ewz, st) := oneHighFamilyEdgeId w z st
  let st := (oneHighFamilyEmit [-(t : Int), (exw : Int)] st).2
  let st := (oneHighFamilyEmit [-(t : Int), (ewz : Int)] st).2
  let st := (oneHighFamilyEmit
    [(t : Int), -(exw : Int), -(ewz : Int)] st).2
  (ts.push (t : Int), st)

theorem oneHighFamilyIdsSound_midpointTseitinStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (ts : Array Int) (x z w : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyMidpointTseitinStep x z w (ts, st)).2 := by
  simp only [oneHighFamilyMidpointTseitinStep]
  generalize h₁ : oneHighFamilyMidpointAtomId x w z st = out₁
  rcases out₁ with ⟨t, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_midpointAtomId h x w z
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyEdgeId x w st₁ = out₂
  rcases out₂ with ⟨exw, st₂⟩
  have hs₂ := oneHighFamilyIdsSound_edgeId hs₁ x w
  rw [h₂] at hs₂
  generalize h₃ : oneHighFamilyEdgeId w z st₂ = out₃
  rcases out₃ with ⟨ewz, st₃⟩
  have hs₃ := oneHighFamilyIdsSound_edgeId hs₂ w z
  rw [h₃] at hs₃
  simp only [h₂, h₃]
  exact oneHighFamilyIdsSound_emit
    (oneHighFamilyIdsSound_emit
      (oneHighFamilyIdsSound_emit hs₃ _) _) _

def oneHighFamilyCommonTseitinStep (bi bj x z : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (cs, st) := accst
  let (ts, st) := (oneHighFamilyPairedMidpoints bi bj).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst) (#[], st)
  let (c, st) := oneHighFamilyCommonAtomId x z st
  let st := (oneHighFamilyEmit (-(c : Int) :: ts.toList) st).2
  let st := ts.foldl
    (fun st t => (oneHighFamilyEmit [-t, (c : Int)] st).2) st
  (cs.push (c : Int), st)

theorem oneHighFamilyIdsSound_commonTseitinStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (cs : Array Int) (bi bj x z : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyCommonTseitinStep bi bj x z (cs, st)).2 := by
  simp only [oneHighFamilyCommonTseitinStep]
  generalize h₁ : (oneHighFamilyPairedMidpoints bi bj).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst)
    (#[], st) = out₁
  rcases out₁ with ⟨ts, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyPairedMidpoints bi bj)
    (fun w accst => oneHighFamilyMidpointTseitinStep x z w accst)
    #[] h (by
      intro w ts st hw
      exact oneHighFamilyIdsSound_midpointTseitinStep hw ts x z w)
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyCommonAtomId x z st₁ = out₂
  rcases out₂ with ⟨c, st₂⟩
  have hs₂ := oneHighFamilyIdsSound_commonAtomId hs₁ x z
  rw [h₂] at hs₂
  have hs₃ := oneHighFamilyIdsSound_emit hs₂ (-(c : Int) :: ts.toList)
  have hs₄ := oneHighFamilyIdsSound_arrayFoldl ts
    (fun st t => (oneHighFamilyEmit [-t, (c : Int)] st).2) hs₃ (by
      intro st t ht
      exact oneHighFamilyIdsSound_emit ht _)
  exact hs₄

def oneHighFamilyInternalEdgesNat (a b : Nat) : Nat :=
  if b % 2 = 0 ∧ b / 2 < a then 1 else 2

def oneHighFamilyPairedProductBlockStep (a pair : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let bi := 2 * pair
  let bj := bi + 1
  let (cs, st) := (oneHighFamilyBlockVertices bi).foldl (fun accst x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep bi bj x z accst) accst)
    (#[], st)
  let bound := 30 - 2 * oneHighFamilyInternalEdgesNat a bi -
    2 * oneHighFamilyInternalEdgesNat a bj
  oneHighFamilyEqualsBlock cs bound st

theorem oneHighFamilyIdsSound_pairedProductBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a pair : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyPairedProductBlockStep a pair st) := by
  simp only [oneHighFamilyPairedProductBlockStep]
  let bi := 2 * pair
  let bj := bi + 1
  generalize heq : (oneHighFamilyBlockVertices bi).foldl (fun accst x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep bi bj x z accst) accst)
    (#[], st) = out
  rcases out with ⟨cs, st'⟩
  apply oneHighFamilyIdsSound_equalsBlock _ cs _
  have hs := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyBlockVertices bi)
    (fun x accst => (oneHighFamilyBlockVertices bj).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep bi bj x z accst) accst)
    #[] h (by
      intro x cs st hx
      exact oneHighFamilyIdsSound_foldlAccum
        (oneHighFamilyBlockVertices bj)
        (fun z accst => oneHighFamilyCommonTseitinStep bi bj x z accst)
        cs hx (by
          intro z cs st hz
          exact oneHighFamilyIdsSound_commonTseitinStep hz cs bi bj x z))
  rw [heq] at hs
  exact hs

/-- Complete PURE family generator. -/
def oneHighFamilyPureClauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 4)
    (oneHighFamilyPairedProductBlockStep a) (oneHighFamilyLexClauses a)

theorem oneHighFamilyIdsSound_pureClauses (a : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyPureClauses a) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_lexClauses a)
    (fun pair st h => oneHighFamilyIdsSound_pairedProductBlockStep h a pair)

theorem oneHighFamilyInternalUnits_reference :
    ∀ a ∈ [0, 1, 2, 3, 4],
      let out := oneHighFamilyInternalUnits a
      out.top = 80 ∧ out.ids.length = 80 ∧ out.clauses.size = 80 := by
  native_decide

theorem oneHighFamilyBaseUnits_reference :
    ∀ a ∈ [0, 1, 2, 3, 4],
      let out := oneHighFamilyBaseUnits a
      out.top = 180 ∧ out.ids.length = 180 ∧ out.clauses.size = 180 := by
  native_decide

/-- Reference prefix for AAAA pins both first-encounter IDs and unit signs. -/
theorem oneHighFamilyInternalUnits_AAAA_prefix :
    (oneHighFamilyInternalUnits 4).clauses.toList.take 10 =
      [[1], [-2], [-3], [-4], [-5], [-6], [-7], [-8], [-9], [-10]] := by
  native_decide

end Erdos85
