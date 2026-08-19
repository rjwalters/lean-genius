import Proofs.Erdos85DimacsSatBridge

/-!
# Finite owner-tiling CNF for the low eight-plus-eight model

This is the exact finite terminal attached to the graph model in
`Erdos85SizeTwoEigenlineEightEightLowExteriorModel`.  The sixteen internal
vertices are numbered by two consecutive C8 shores.  The forty-eight owner
pairs are the edges of the exterior-pair graph: offset `±3` within a shore
and opposite parity across shores.
-/

namespace Erdos85

open Std Sat

abbrev EightEightOwner := Nat × Nat

def eightEightSameShore (a b : Nat) : Bool := a / 8 == b / 8

def eightEightCycleAdj (a b : Nat) : Bool :=
  eightEightSameShore a b && (((a + 1) % 8 == b % 8) || ((b + 1) % 8 == a % 8))

def eightEightLowOwnerPair (a b : Nat) : Bool :=
  a < b && (if eightEightSameShore a b then
    ((b + 8 - a) % 8 == 3) || ((b + 8 - a) % 8 == 5)
  else
    a % 2 != b % 2)

def eightEightLowOwners : List EightEightOwner :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => eightEightLowOwnerPair a b).map fun b => (a, b)

def eightEightOwnerAt (e : Nat) : EightEightOwner :=
  (eightEightLowOwners[e]?).getD (0, 0)

def eightEightOwnerContains (e v : Nat) : Bool :=
  let p := eightEightOwnerAt e
  p.1 == v || p.2 == v

def eightEightOwnerTargetContains (e v : Nat) : Bool :=
  let p := eightEightOwnerAt e
  !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v

def eightEightOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    eightEightOwnerTargetContains e (eightEightOwnerAt f).1 &&
    eightEightOwnerTargetContains e (eightEightOwnerAt f).2 &&
    eightEightOwnerTargetContains f (eightEightOwnerAt e).1 &&
    eightEightOwnerTargetContains f (eightEightOwnerAt e).2

def eightEightOwnerVariables : List (Nat × Nat) :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f && eightEightOwnerCompatible e f).map
      fun f => (e, f)

def eightEightOwnerVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (eightEightOwnerVariables.idxOf? p).map (· + 1)

def eightEightOwnerLiteral? (e f : Nat) : Option Int :=
  (eightEightOwnerVariable? e f).map Int.ofNat

def eightEightOwnerServiceVariables (e v : Nat) : List Int :=
  (List.range 48).filterMap fun f =>
    if f != e && eightEightOwnerContains f v then
      eightEightOwnerLiteral? e f
    else none

def eightEightPairwiseNegativeClauses (xs : List Int) : List DimacsClause :=
  xs.flatMap fun x => (xs.filter fun y => x < y).map fun y => [-x, -y]

def eightEightOwnerServiceClauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := eightEightOwnerAt e
      if !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v then
        let xs := eightEightOwnerServiceVariables e v
        [xs] ++ eightEightPairwiseNegativeClauses xs
      else []

def eightEightOwnersIntersect (e f : Nat) : Bool :=
  let p := eightEightOwnerAt e
  eightEightOwnerContains f p.1 || eightEightOwnerContains f p.2

def eightEightOwnerCommonCandidates (e f : Nat) : List Nat :=
  (List.range 48).filter fun k => k != e && k != f &&
    (eightEightOwnerVariable? e k).isSome &&
    (eightEightOwnerVariable? f k).isSome

def eightEightOwnerNoCommonClauses (e f : Nat) : List DimacsClause :=
  (eightEightOwnerCommonCandidates e f).filterMap fun k => do
    let x ← eightEightOwnerLiteral? e k
    let y ← eightEightOwnerLiteral? f k
    return [-x, -y]

def eightEightOwnerAtMostOneCommonClauses (e f : Nat) : List DimacsClause :=
  let ks := eightEightOwnerCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← eightEightOwnerLiteral? e k
    let xfk ← eightEightOwnerLiteral? f k
    let xel ← eightEightOwnerLiteral? e l
    let xfl ← eightEightOwnerLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def eightEightOwnerC4Clauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f).flatMap fun f =>
      if eightEightOwnersIntersect e f then
        eightEightOwnerNoCommonClauses e f
      else
        eightEightOwnerAtMostOneCommonClauses e f

def eightEightLowOwnerDimacsClauses : Array DimacsClause :=
  (eightEightOwnerServiceClauses ++ eightEightOwnerC4Clauses).toArray

def eightEightLowOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses eightEightLowOwnerDimacsClauses

set_option maxHeartbeats 0 in
theorem eightEightLowOwners_size : eightEightLowOwners.length = 48 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightOwnerVariables_size : eightEightOwnerVariables.length = 640 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightLowOwnerDimacsClauses_size :
    eightEightLowOwnerDimacsClauses.size = 86384 := by
  native_decide

end Erdos85
