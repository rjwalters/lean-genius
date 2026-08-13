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

def oneHighFamilyLookup (atom : OneHighFamilyAtom) :
    List (OneHighFamilyAtom × Nat) → Option Nat
  | [] => none
  | entry :: rest =>
      if entry.1 = atom then some entry.2 else oneHighFamilyLookup atom rest

/-- PySAT `IDPool.id`: named atoms are memoized, while the next fresh ID is
strictly above the current global top (including prior counter auxiliaries). -/
def oneHighFamilyAtomId (atom : OneHighFamilyAtom) :
    StateM OneHighFamilyGenState Nat := fun st =>
  match oneHighFamilyLookup atom st.ids with
  | some id => (id, st)
  | none =>
      let id := st.top + 1
      (id, { st with top := id, ids := (atom, id) :: st.ids })

def oneHighFamilyEdgeId (i j : Nat) : StateM OneHighFamilyGenState Nat :=
  oneHighFamilyAtomId (.edge (min i j) (max i j))

def oneHighFamilyEmit (clause : DimacsClause) :
    StateM OneHighFamilyGenState Unit :=
  modify fun st => { st with clauses := st.clauses.push clause }

def oneHighFamilyRunList {α : Type} (xs : List α)
    (step : α → OneHighFamilyGenState → OneHighFamilyGenState)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  xs.foldl (fun st x => step x st) st

def oneHighFamilyInternalPairStep (a b i j : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (id, st) := oneHighFamilyEdgeId (5 * b + i) (5 * b + j) st
  let twoEdges := ¬(b % 2 = 0 ∧ b / 2 < a)
  let present := (i = 0 ∧ j = 1) ∨ (twoEdges ∧ i = 2 ∧ j = 3)
  (oneHighFamilyEmit [if present then (id : Int) else -(id : Int)] st).2

def oneHighFamilyInternalBlockStep (a b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 5) (fun i st =>
    oneHighFamilyRunList (List.range 5) (fun j st =>
      if i < j then oneHighFamilyInternalPairStep a b i j st else st) st) st

/-- First generator segment: the 80 within-block matching unit clauses. -/
def oneHighFamilyInternalUnits (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) (oneHighFamilyInternalBlockStep a) {}

def oneHighFamilyMatePairStep (b i j : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (id, st) := oneHighFamilyEdgeId (5 * b + i) (5 * (b + 1) + j) st
  (oneHighFamilyEmit [-(id : Int)] st).2

def oneHighFamilyMateBlockStep (b : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 5) (fun i st =>
    oneHighFamilyRunList (List.range 5)
      (fun j st => oneHighFamilyMatePairStep b i j st) st) st

/-- Second generator segment: the 100 zero units between standard-mate
blocks, starting from the completed internal-unit state. -/
def oneHighFamilyBaseUnits (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList [0, 2, 4, 6] oneHighFamilyMateBlockStep
    (oneHighFamilyInternalUnits a)

def oneHighFamilyC4SameMidpointStep (i j w : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (eiw, st) := oneHighFamilyEdgeId i w st
  let (ejw, st) := oneHighFamilyEdgeId j w st
  (oneHighFamilyEmit [-(eiw : Int), -(ejw : Int)] st).2

def oneHighFamilyC4CrossMidpointsStep (i j w w' : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (eiw, st) := oneHighFamilyEdgeId i w st
  let (ejw, st) := oneHighFamilyEdgeId j w st
  let (eiw', st) := oneHighFamilyEdgeId i w' st
  let (ejw', st) := oneHighFamilyEdgeId j w' st
  (oneHighFamilyEmit
    [-(eiw : Int), -(ejw : Int), -(eiw' : Int), -(ejw' : Int)] st).2

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

def oneHighFamilyC4OuterStep (i : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) (fun j st =>
    if i < j then oneHighFamilyC4PairStep i j st else st) st

/-- Third generator segment: same-block zero-common-neighbor clauses and
general cross-block at-most-one-common-neighbor clauses, in the exact nested
`itertools.combinations` order. -/
def oneHighFamilyC4Clauses (a : Nat) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) oneHighFamilyC4OuterStep
    (oneHighFamilyBaseUnits a)

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem oneHighFamilyC4Clauses_reference :
    let out := oneHighFamilyC4Clauses 4
    out.top = 780 ∧ out.ids.length = 780 ∧ out.clauses.size = 495320 := by
  native_decide

/-- Reference prefix for AAAA pins both first-encounter IDs and unit signs. -/
theorem oneHighFamilyInternalUnits_AAAA_prefix :
    (oneHighFamilyInternalUnits 4).clauses.toList.take 10 =
      [[1], [-2], [-3], [-4], [-5], [-6], [-7], [-8], [-9], [-10]] := by
  native_decide

end Erdos85
