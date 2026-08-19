import Proofs.Erdos85EightEightLowOwnerCnf

/-!
# Finite owner-tiling CNF for the both-all-triangle eight-plus-eight model

Each C8 shore is all-triangle and has exterior-pair offsets
`±1`.
Cross-shore exterior pairs join opposite parity.  The service and C4 clause
families are identical to the checked low-model encoding.
-/

namespace Erdos85

open Std Sat

def eightEightBothTriangleOwnerPair (a b : Nat) : Bool :=
  a < b && (if eightEightSameShore a b then
    ((b + 8 - a) % 8 == 1) || ((b + 8 - a) % 8 == 7)
  else
    a % 2 != b % 2)

def eightEightBothTriangleOwners : List EightEightOwner :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => eightEightBothTriangleOwnerPair a b).map
      fun b => (a, b)

def eightEightBothTriangleOwnerAt (e : Nat) : EightEightOwner :=
  (eightEightBothTriangleOwners[e]?).getD (0, 0)

def eightEightBothTriangleOwnerContains (e v : Nat) : Bool :=
  let p := eightEightBothTriangleOwnerAt e
  p.1 == v || p.2 == v

def eightEightBothTriangleOwnerTargetContains (e v : Nat) : Bool :=
  let p := eightEightBothTriangleOwnerAt e
  !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v

def eightEightBothTriangleOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    eightEightBothTriangleOwnerTargetContains e (eightEightBothTriangleOwnerAt f).1 &&
    eightEightBothTriangleOwnerTargetContains e (eightEightBothTriangleOwnerAt f).2 &&
    eightEightBothTriangleOwnerTargetContains f (eightEightBothTriangleOwnerAt e).1 &&
    eightEightBothTriangleOwnerTargetContains f (eightEightBothTriangleOwnerAt e).2

def eightEightBothTriangleOwnerVariables : List (Nat × Nat) :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f =>
      e < f && eightEightBothTriangleOwnerCompatible e f).map fun f => (e, f)

def eightEightBothTriangleOwnerVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (eightEightBothTriangleOwnerVariables.idxOf? p).map (· + 1)

def eightEightBothTriangleOwnerLiteral? (e f : Nat) : Option Int :=
  (eightEightBothTriangleOwnerVariable? e f).map Int.ofNat

def eightEightBothTriangleOwnerServiceVariables (e v : Nat) : List Int :=
  (List.range 48).filterMap fun f =>
    if f != e && eightEightBothTriangleOwnerContains f v then
      eightEightBothTriangleOwnerLiteral? e f
    else none

def eightEightBothTriangleOwnerServiceClauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := eightEightBothTriangleOwnerAt e
      if !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v then
        let xs := eightEightBothTriangleOwnerServiceVariables e v
        [xs] ++ eightEightPairwiseNegativeClauses xs
      else []

def eightEightBothTriangleOwnersIntersect (e f : Nat) : Bool :=
  let p := eightEightBothTriangleOwnerAt e
  eightEightBothTriangleOwnerContains f p.1 ||
    eightEightBothTriangleOwnerContains f p.2

def eightEightBothTriangleOwnerCommonCandidates (e f : Nat) : List Nat :=
  (List.range 48).filter fun k => k != e && k != f &&
    (eightEightBothTriangleOwnerVariable? e k).isSome &&
    (eightEightBothTriangleOwnerVariable? f k).isSome

def eightEightBothTriangleOwnerNoCommonClauses (e f : Nat) : List DimacsClause :=
  (eightEightBothTriangleOwnerCommonCandidates e f).filterMap fun k => do
    let x ← eightEightBothTriangleOwnerLiteral? e k
    let y ← eightEightBothTriangleOwnerLiteral? f k
    return [-x, -y]

def eightEightBothTriangleOwnerAtMostOneCommonClauses
    (e f : Nat) : List DimacsClause :=
  let ks := eightEightBothTriangleOwnerCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← eightEightBothTriangleOwnerLiteral? e k
    let xfk ← eightEightBothTriangleOwnerLiteral? f k
    let xel ← eightEightBothTriangleOwnerLiteral? e l
    let xfl ← eightEightBothTriangleOwnerLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def eightEightBothTriangleOwnerC4Clauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f).flatMap fun f =>
      if eightEightBothTriangleOwnersIntersect e f then
        eightEightBothTriangleOwnerNoCommonClauses e f
      else
        eightEightBothTriangleOwnerAtMostOneCommonClauses e f

def eightEightBothTriangleOwnerDimacsClauses : Array DimacsClause :=
  (eightEightBothTriangleOwnerServiceClauses ++
    eightEightBothTriangleOwnerC4Clauses).toArray

def eightEightBothTriangleOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses eightEightBothTriangleOwnerDimacsClauses

set_option maxHeartbeats 0 in
theorem eightEightBothTriangleOwners_size : eightEightBothTriangleOwners.length = 48 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightBothTriangleOwnerVariables_size :
    eightEightBothTriangleOwnerVariables.length = 648 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightBothTriangleOwnerDimacsClauses_size :
    eightEightBothTriangleOwnerDimacsClauses.size = 89584 := by
  native_decide

end Erdos85
