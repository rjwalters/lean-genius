import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85SequentialCounterGenerator

/-!
# Exact CNF generator for the seven `h = 7, t = 0` cubes

This is an executable transcription of `generate_h7_t0_cubes.py`, including
PySAT's named `IDPool` allocation order and sequential-counter auxiliaries.
The cube index selects the unique neighbor of vertex `9` in `15..21`.
-/

namespace Erdos85

inductive SevenHighT0CubeAtom where
  | edge : Nat → Nat → SevenHighT0CubeAtom
  | common : Nat → Nat → Nat → SevenHighT0CubeAtom
deriving DecidableEq, Repr

structure SevenHighT0CubeGenState where
  top : Nat := 0
  ids : List (SevenHighT0CubeAtom × Nat) := []
  clauses : Array DimacsClause := #[]
deriving Repr, DecidableEq

def sevenHighT0CubeLookup (atom : SevenHighT0CubeAtom) :
    List (SevenHighT0CubeAtom × Nat) → Option Nat
  | [] => none
  | entry :: rest =>
      if entry.1 = atom then some entry.2
      else sevenHighT0CubeLookup atom rest

def sevenHighT0CubeAtomId (atom : SevenHighT0CubeAtom)
    (st : SevenHighT0CubeGenState) : Nat × SevenHighT0CubeGenState :=
  match sevenHighT0CubeLookup atom st.ids with
  | some id => (id, st)
  | none =>
      let id := st.top + 1
      (id, { st with top := id, ids := (atom, id) :: st.ids })

def sevenHighT0CubeEdgeId (i j : Nat)
    (st : SevenHighT0CubeGenState) : Nat × SevenHighT0CubeGenState :=
  sevenHighT0CubeAtomId (.edge (min i j) (max i j)) st

def sevenHighT0CubeCommonId (i j w : Nat)
    (st : SevenHighT0CubeGenState) : Nat × SevenHighT0CubeGenState :=
  sevenHighT0CubeAtomId (.common i j w) st

def sevenHighT0CubeEmit (clause : DimacsClause)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  { st with clauses := st.clauses.push clause }

def sevenHighT0CubePairs (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap fun a =>
    (xs.filter fun b => a < b).map fun b => (a, b)

def sevenHighT0CubeHighs : List Nat := List.range 7
def sevenHighT0CubeVertices : List Nat := List.range 49
def sevenHighT0CubeLows : List Nat := (List.range 42).map (· + 7)
def sevenHighT0CubeN0 : List Nat := (List.range 8).map (· + 7)
def sevenHighT0CubeN1 : List Nat := 7 :: (List.range 7).map (· + 15)

def sevenHighT0CubeMatching0 (a b : Nat) : Bool :=
  (a = 7 && b = 8) || (a = 9 && b = 10) ||
    (a = 11 && b = 12) || (a = 13 && b = 14)

def sevenHighT0CubeMatching1 (a b : Nat) : Bool :=
  (a = 7 && b = 15) || (a = 16 && b = 17) ||
    (a = 18 && b = 19) || (a = 20 && b = 21)

def sevenHighT0CubeEmitEdgeUnit (i j : Nat) (positive : Bool)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let (id, st) := sevenHighT0CubeEdgeId i j st
  sevenHighT0CubeEmit [if positive then (id : Int) else -(id : Int)] st

def sevenHighT0CubeHighIndependent : SevenHighT0CubeGenState :=
  (sevenHighT0CubePairs sevenHighT0CubeHighs).foldl (fun st pair =>
    sevenHighT0CubeEmitEdgeUnit pair.1 pair.2 false st) {}

def sevenHighT0CubeNormalizeN0 : SevenHighT0CubeGenState :=
  let st := sevenHighT0CubeLows.foldl (fun st x =>
    sevenHighT0CubeEmitEdgeUnit 0 x (x < 15) st)
    sevenHighT0CubeHighIndependent
  (sevenHighT0CubePairs sevenHighT0CubeN0).foldl (fun st pair =>
    sevenHighT0CubeEmitEdgeUnit pair.1 pair.2
      (sevenHighT0CubeMatching0 pair.1 pair.2) st) st

def sevenHighT0CubeNormalizeN1 : SevenHighT0CubeGenState :=
  let st := sevenHighT0CubeEmitEdgeUnit 1 7 true sevenHighT0CubeNormalizeN0
  let st := (List.range 7).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 8) false st) st
  let st := (List.range 7).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 15) true st) st
  let st := (List.range 27).foldl (fun st k =>
    sevenHighT0CubeEmitEdgeUnit 1 (k + 22) false st) st
  (sevenHighT0CubePairs sevenHighT0CubeN1).foldl (fun st pair =>
    sevenHighT0CubeEmitEdgeUnit pair.1 pair.2
      (sevenHighT0CubeMatching1 pair.1 pair.2) st) st

def sevenHighT0CubeCommonPairStep (pair : Nat × Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let (common, st) := sevenHighT0CubeLows.foldl (fun (acc, st) w =>
    let (aux, st) := sevenHighT0CubeCommonId pair.1 pair.2 w st
    let (iw, st) := sevenHighT0CubeEdgeId pair.1 w st
    let (jw, st) := sevenHighT0CubeEdgeId pair.2 w st
    let st := sevenHighT0CubeEmit [-(aux : Int), (iw : Int)] st
    let st := sevenHighT0CubeEmit [-(aux : Int), (jw : Int)] st
    (acc ++ [(aux : Int)], st)) ([], st)
  sevenHighT0CubeEmit common st

def sevenHighT0CubeCommonClauses : SevenHighT0CubeGenState :=
  (sevenHighT0CubePairs sevenHighT0CubeHighs).foldl
    (fun st pair => sevenHighT0CubeCommonPairStep pair st)
    sevenHighT0CubeNormalizeN1

def sevenHighT0CubeC4PairStep (pair : Nat × Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let others := sevenHighT0CubeVertices.filter fun w =>
    w ≠ pair.1 && w ≠ pair.2
  (sevenHighT0CubePairs others).foldl (fun st witnesses =>
    let (iw, st) := sevenHighT0CubeEdgeId pair.1 witnesses.1 st
    let (jw, st) := sevenHighT0CubeEdgeId pair.2 witnesses.1 st
    let (iw', st) := sevenHighT0CubeEdgeId pair.1 witnesses.2 st
    let (jw', st) := sevenHighT0CubeEdgeId pair.2 witnesses.2 st
    sevenHighT0CubeEmit
      [-(iw : Int), -(jw : Int), -(iw' : Int), -(jw' : Int)] st) st

def sevenHighT0CubeC4Clauses : SevenHighT0CubeGenState :=
  (sevenHighT0CubePairs sevenHighT0CubeVertices).foldl
    (fun st pair => sevenHighT0CubeC4PairStep pair st)
    sevenHighT0CubeCommonClauses

def sevenHighT0CubeDegreeStep (vertex : Nat)
    (st : SevenHighT0CubeGenState) : SevenHighT0CubeGenState :=
  let incident := sevenHighT0CubeVertices.filter fun x => x ≠ vertex
  let (vars, st) := incident.foldl (fun (acc, st) x =>
    let (id, st) := sevenHighT0CubeEdgeId vertex x st
    (acc.push (id : Int), st)) (#[], st)
  let out := seqCounterEquals st.top vars (if vertex < 7 then 8 else 7)
  { st with top := out.top, clauses := st.clauses ++ out.clauses }

def sevenHighT0CubeDegreeClauses : SevenHighT0CubeGenState :=
  sevenHighT0CubeVertices.foldl
    (fun st vertex => sevenHighT0CubeDegreeStep vertex st)
    sevenHighT0CubeC4Clauses

def sevenHighT0CubePartitionNeighbors (high : Nat) : List Nat :=
  if high = 0 then sevenHighT0CubeN0 else sevenHighT0CubeN1

def sevenHighT0CubePartitionClauses : SevenHighT0CubeGenState :=
  sevenHighT0CubeLows.foldl (fun st y =>
    [0, 1].foldl (fun st high =>
      let (clause, st) :=
        (sevenHighT0CubePartitionNeighbors high).foldl (fun (acc, st) x =>
          if x = y then (acc, st) else
            let (id, st) := sevenHighT0CubeEdgeId y x st
            (acc ++ [(id : Int)], st)) ([], st)
      sevenHighT0CubeEmit clause st) st) sevenHighT0CubeDegreeClauses

def sevenHighT0CubeFinalState (cube : Nat) : SevenHighT0CubeGenState :=
  (List.range 7).foldl (fun st index =>
    sevenHighT0CubeEmitEdgeUnit 9 (index + 15) (index = cube) st)
    sevenHighT0CubePartitionClauses

def orderFortyNineGeneratedH7T0CubeSatCnf (cube : Nat) : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses (sevenHighT0CubeFinalState cube).clauses

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CubeFinalState_shapes :
    (List.range 7).all (fun cube =>
      (sevenHighT0CubeFinalState cube).top == 30646 &&
      (sevenHighT0CubeFinalState cube).clauses.size == 1330469) = true := by
  native_decide

end Erdos85
