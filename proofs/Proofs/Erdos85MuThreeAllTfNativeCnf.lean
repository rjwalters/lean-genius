import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85SequentialCounterGenerator

/-! # Lean-native CNF for the all-triangle-free `mu = 3` grid

This is the executable mirror of `mu3grid/generate_alltf_native_cnf.py`.
Its allocation order is deliberately transparent and independent of an
external solver's preprocessing.
-/

namespace Erdos85

inductive Mu3AllTfShape where
  | c16
  | c10c6
  | c8c8
deriving DecidableEq, Repr

structure Mu3NativeCnfState where
  top : Nat := 1128
  clauses : Array DimacsClause := #[]
deriving DecidableEq, Repr

def mu3AllTfInternal (shape : Mu3AllTfShape) (x y : Nat) : Bool :=
  match shape with
  | .c16 => y = x || y = (x + 7) % 8
  | .c10c6 =>
      if x < 5 then y = x || y = (x + 4) % 5
      else y = x || y = 5 + ((x - 5 + 2) % 3)
  | .c8c8 =>
      if x < 4 then y = x || y = (x + 3) % 4
      else y = x || y = 4 + ((x - 4 + 3) % 4)

def mu3AllTfCells (shape : Mu3AllTfShape) : List Nat :=
  (List.range 64).filter fun z => !mu3AllTfInternal shape (z / 8) (z % 8)

def mu3NativePairs : List (Nat × Nat) :=
  (List.range 48).flatMap fun u =>
    ((List.range (47 - u)).map fun k => (u, u + k + 1))

def mu3NativeEdgeId (u v : Nat) : Nat :=
  mu3NativePairs.idxOf (min u v, max u v) + 1

def mu3NativeEmit (clause : DimacsClause)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  { st with clauses := st.clauses.push clause }

def mu3NativeFresh (st : Mu3NativeCnfState) : Nat × Mu3NativeCnfState :=
  let id := st.top + 1
  (id, { st with top := id })

def mu3NativeAppendCounter (out : SeqCounterGenState)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  { top := out.top, clauses := st.clauses ++ out.clauses }

def mu3NativeEquals (vars : Array Int) (target : Nat)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  mu3NativeAppendCounter (seqCounterEquals st.top vars target) st

def mu3NativeAtMost (vars : Array Int) (target : Nat)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  mu3NativeAppendCounter (seqCounterAtMost st.top vars target) st

def mu3NativeCellIndex (shape : Mu3AllTfShape) (cell : Nat) : Nat :=
  (mu3AllTfCells shape).idxOf cell

def mu3NativeRowVars (shape : Mu3AllTfShape) (u x : Nat) : Array Int :=
  let cells := mu3AllTfCells shape
  (cells.filter fun cell => cell / 8 = x && mu3NativeCellIndex shape cell ≠ u).toArray.map
    fun cell => (mu3NativeEdgeId u (mu3NativeCellIndex shape cell) : Int)

def mu3NativeColumnVars (shape : Mu3AllTfShape) (u y : Nat) : Array Int :=
  let cells := mu3AllTfCells shape
  (cells.filter fun cell => cell % 8 = y && mu3NativeCellIndex shape cell ≠ u).toArray.map
    fun cell => (mu3NativeEdgeId u (mu3NativeCellIndex shape cell) : Int)

def mu3NativeHitBlocks (shape : Mu3AllTfShape) : Mu3NativeCnfState :=
  (List.range 48).foldl (fun st u =>
    let cell := (mu3AllTfCells shape).getD u 0
    let xu := cell / 8
    let yu := cell % 8
    let st := (List.range 8).foldl (fun st x =>
      mu3NativeEquals (mu3NativeRowVars shape u x)
        (if mu3AllTfInternal shape x yu then 0 else 1) st) st
    (List.range 8).foldl (fun st y =>
      mu3NativeEquals (mu3NativeColumnVars shape u y)
        (if mu3AllTfInternal shape xu y then 0 else 1) st) st) {}

def mu3NativeCommonStep (u v m : Nat)
    (acc : Array Int × Mu3NativeCnfState) : Array Int × Mu3NativeCnfState :=
  if m = u || m = v then acc
  else
    let (aux, st) := mu3NativeFresh acc.2
    let eum : Int := mu3NativeEdgeId u m
    let evm : Int := mu3NativeEdgeId v m
    let st := mu3NativeEmit [-(aux : Int), eum] st
    let st := mu3NativeEmit [-(aux : Int), evm] st
    let st := mu3NativeEmit [-eum, -evm, (aux : Int)] st
    (acc.1.push (aux : Int), st)

def mu3NativeC4PairStep (pair : Nat × Nat)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  let (common, st) := (List.range 48).foldl
    (fun acc m => mu3NativeCommonStep pair.1 pair.2 m acc) (#[], st)
  mu3NativeAtMost common 1 st

def mu3NativeFinalState (shape : Mu3AllTfShape) : Mu3NativeCnfState :=
  mu3NativePairs.foldl (fun st pair => mu3NativeC4PairStep pair st)
    (mu3NativeHitBlocks shape)

def mu3AllTfNativeSatCnf (shape : Mu3AllTfShape) : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses (mu3NativeFinalState shape).clauses

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem mu3NativeFinalState_shapes :
    ([Mu3AllTfShape.c16, .c10c6, .c8c8].all fun shape =>
      (mu3AllTfCells shape).length == 48 &&
      (mu3NativeFinalState shape).top == 106560 &&
      (mu3NativeFinalState shape).clauses.size == 316320) = true := by
  native_decide

end Erdos85
