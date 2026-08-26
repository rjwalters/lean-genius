import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85SequentialCounterGenerator

/-!
# Compact canonical CNF for the H7/T0 completion problem

This is the Lean transcription of
`check_h7_t0_canonical_compact.py`.  Vertices use the reviewed canonical
order: highs `0..6`, empty-support lows `7..13`, singleton lows `14..27`,
and pair-support lows `28..48`.  Variables `1..861` are the lexicographically
ordered low-low edges.  Exact low degrees use the already reified compact
`seqCounterEquals` generator, after which the global C4 clauses are emitted
in endpoint-pair / common-neighbor-pair order.
-/

namespace Erdos85

def sevenHighT0CanonicalNatPairs (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap fun a => (xs.filter fun b => a < b).map fun b => (a, b)

def sevenHighT0CanonicalHighs : List Nat := List.range 7
def sevenHighT0CanonicalEmpties : List Nat := (List.range 7).map (· + 7)
def sevenHighT0CanonicalSingletons : List Nat := (List.range 14).map (· + 14)
def sevenHighT0CanonicalPairs : List Nat := (List.range 21).map (· + 28)
def sevenHighT0CanonicalLows : List Nat := (List.range 42).map (· + 7)
def sevenHighT0CanonicalVertices : List Nat := List.range 49
def sevenHighT0CanonicalLabelPairs : List (Nat × Nat) :=
  sevenHighT0CanonicalNatPairs sevenHighT0CanonicalHighs

def sevenHighT0CanonicalLowEdgePairs : List (Nat × Nat) :=
  sevenHighT0CanonicalNatPairs sevenHighT0CanonicalLows

def sevenHighT0CanonicalLowEdgeId (a b : Nat) : Nat :=
  let edge := (min a b, max a b)
  sevenHighT0CanonicalLowEdgePairs.idxOf edge + 1

def sevenHighT0CanonicalHighLowFixed (high low : Nat) : Bool :=
  if 14 ≤ low ∧ low < 28 then
    high = (low - 14) / 2
  else if 28 ≤ low ∧ low < 49 then
    match sevenHighT0CanonicalLabelPairs[low - 28]? with
    | some labels => high = labels.1 || high = labels.2
    | none => false
  else false

inductive SevenHighT0CanonicalEdgeStatus where
  | fixedFalse
  | fixedTrue
  | variable (id : Nat)
deriving Repr, DecidableEq

def sevenHighT0CanonicalEdgeStatus (a b : Nat) :
    SevenHighT0CanonicalEdgeStatus :=
  if a = b then .fixedFalse
  else if 7 ≤ a ∧ 7 ≤ b then
    .variable (sevenHighT0CanonicalLowEdgeId a b)
  else if a < 7 then
    if sevenHighT0CanonicalHighLowFixed a b then .fixedTrue else .fixedFalse
  else if b < 7 then
    if sevenHighT0CanonicalHighLowFixed b a then .fixedTrue else .fixedFalse
  else .fixedFalse

structure SevenHighT0CanonicalCnfState where
  top : Nat := 861
  clauses : Array DimacsClause := #[]
deriving Repr, DecidableEq

def sevenHighT0CanonicalLowDegree (vertex : Nat) : Nat :=
  if vertex < 14 then 7 else if vertex < 28 then 6 else 5

def sevenHighT0CanonicalDegreeStep (vertex : Nat)
    (st : SevenHighT0CanonicalCnfState) : SevenHighT0CanonicalCnfState :=
  let incident := (sevenHighT0CanonicalLows.filter fun other => other ≠ vertex).toArray.map
    fun other => (sevenHighT0CanonicalLowEdgeId vertex other : Int)
  let out := seqCounterEquals st.top incident
    (sevenHighT0CanonicalLowDegree vertex)
  { top := out.top, clauses := st.clauses ++ out.clauses }

def sevenHighT0CanonicalDegreeState : SevenHighT0CanonicalCnfState :=
  sevenHighT0CanonicalLows.foldl
    (fun st vertex => sevenHighT0CanonicalDegreeStep vertex st) {}

def sevenHighT0CanonicalC4Literal :
    SevenHighT0CanonicalEdgeStatus → Option Int
  | .fixedFalse => none
  | .fixedTrue => none
  | .variable id => some (-(id : Int))

def sevenHighT0CanonicalC4Step (endpoints witnesses : Nat × Nat)
    (st : SevenHighT0CanonicalCnfState) : SevenHighT0CanonicalCnfState :=
  let statuses :=
    [sevenHighT0CanonicalEdgeStatus endpoints.1 witnesses.1,
     sevenHighT0CanonicalEdgeStatus endpoints.2 witnesses.1,
     sevenHighT0CanonicalEdgeStatus endpoints.1 witnesses.2,
     sevenHighT0CanonicalEdgeStatus endpoints.2 witnesses.2]
  if statuses.contains .fixedFalse then st
  else
    { st with
      clauses := st.clauses.push
        (statuses.filterMap sevenHighT0CanonicalC4Literal) }

def sevenHighT0CanonicalC4EndpointStep (endpoints : Nat × Nat)
    (st : SevenHighT0CanonicalCnfState) : SevenHighT0CanonicalCnfState :=
  let candidates := sevenHighT0CanonicalVertices.filter fun vertex =>
    vertex ≠ endpoints.1 && vertex ≠ endpoints.2
  (sevenHighT0CanonicalNatPairs candidates).foldl
    (fun st witnesses => sevenHighT0CanonicalC4Step endpoints witnesses st) st

def sevenHighT0CanonicalFinalState : SevenHighT0CanonicalCnfState :=
  (sevenHighT0CanonicalNatPairs sevenHighT0CanonicalVertices).foldl
    (fun st endpoints => sevenHighT0CanonicalC4EndpointStep endpoints st)
    sevenHighT0CanonicalDegreeState

def orderFortyNineSevenHighT0CanonicalSatCnf : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses sevenHighT0CanonicalFinalState.clauses

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CanonicalFinalState_shape :
    sevenHighT0CanonicalFinalState.top = 17633 ∧
      sevenHighT0CanonicalFinalState.clauses.size = 720804 := by
  native_decide

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalFinalState_shape
