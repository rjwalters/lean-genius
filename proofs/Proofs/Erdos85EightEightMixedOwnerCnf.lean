import Proofs.Erdos85EightEightLowOwnerCnf

/-!
# Finite owner-tiling CNF for the mixed eight-plus-eight model

The first C8 shore is all-triangle-free and has exterior-pair offsets
`±3`; the second is all-triangle and has exterior-pair offsets `±1`.
Cross-shore exterior pairs join opposite parity.  The service and C4 clause
families are identical to the checked low-model encoding.
-/

namespace Erdos85

open Std Sat

def eightEightMixedOwnerPair (a b : Nat) : Bool :=
  a < b && (if eightEightSameShore a b then
    if a / 8 == 0 then
      ((b + 8 - a) % 8 == 3) || ((b + 8 - a) % 8 == 5)
    else
      ((b + 8 - a) % 8 == 1) || ((b + 8 - a) % 8 == 7)
  else
    a % 2 != b % 2)

def eightEightMixedOwners : List EightEightOwner :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => eightEightMixedOwnerPair a b).map
      fun b => (a, b)

def eightEightMixedOwnerAt (e : Nat) : EightEightOwner :=
  (eightEightMixedOwners[e]?).getD (0, 0)

def eightEightMixedOwnerContains (e v : Nat) : Bool :=
  let p := eightEightMixedOwnerAt e
  p.1 == v || p.2 == v

def eightEightMixedOwnerTargetContains (e v : Nat) : Bool :=
  let p := eightEightMixedOwnerAt e
  !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v

def eightEightMixedOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    eightEightMixedOwnerTargetContains e (eightEightMixedOwnerAt f).1 &&
    eightEightMixedOwnerTargetContains e (eightEightMixedOwnerAt f).2 &&
    eightEightMixedOwnerTargetContains f (eightEightMixedOwnerAt e).1 &&
    eightEightMixedOwnerTargetContains f (eightEightMixedOwnerAt e).2

def eightEightMixedOwnerVariables : List (Nat × Nat) :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f =>
      e < f && eightEightMixedOwnerCompatible e f).map fun f => (e, f)

def eightEightMixedOwnerVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (eightEightMixedOwnerVariables.idxOf? p).map (· + 1)

def eightEightMixedOwnerLiteral? (e f : Nat) : Option Int :=
  (eightEightMixedOwnerVariable? e f).map Int.ofNat

def eightEightMixedOwnerServiceVariables (e v : Nat) : List Int :=
  (List.range 48).filterMap fun f =>
    if f != e && eightEightMixedOwnerContains f v then
      eightEightMixedOwnerLiteral? e f
    else none

def eightEightMixedOwnerServiceClauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := eightEightMixedOwnerAt e
      if !eightEightCycleAdj p.1 v && !eightEightCycleAdj p.2 v then
        let xs := eightEightMixedOwnerServiceVariables e v
        [xs] ++ eightEightPairwiseNegativeClauses xs
      else []

def eightEightMixedOwnersIntersect (e f : Nat) : Bool :=
  let p := eightEightMixedOwnerAt e
  eightEightMixedOwnerContains f p.1 ||
    eightEightMixedOwnerContains f p.2

def eightEightMixedOwnerCommonCandidates (e f : Nat) : List Nat :=
  (List.range 48).filter fun k => k != e && k != f &&
    (eightEightMixedOwnerVariable? e k).isSome &&
    (eightEightMixedOwnerVariable? f k).isSome

def eightEightMixedOwnerNoCommonClauses (e f : Nat) : List DimacsClause :=
  (eightEightMixedOwnerCommonCandidates e f).filterMap fun k => do
    let x ← eightEightMixedOwnerLiteral? e k
    let y ← eightEightMixedOwnerLiteral? f k
    return [-x, -y]

def eightEightMixedOwnerAtMostOneCommonClauses
    (e f : Nat) : List DimacsClause :=
  let ks := eightEightMixedOwnerCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← eightEightMixedOwnerLiteral? e k
    let xfk ← eightEightMixedOwnerLiteral? f k
    let xel ← eightEightMixedOwnerLiteral? e l
    let xfl ← eightEightMixedOwnerLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def eightEightMixedOwnerC4Clauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f).flatMap fun f =>
      if eightEightMixedOwnersIntersect e f then
        eightEightMixedOwnerNoCommonClauses e f
      else
        eightEightMixedOwnerAtMostOneCommonClauses e f

def eightEightMixedOwnerDimacsClauses : Array DimacsClause :=
  (eightEightMixedOwnerServiceClauses ++
    eightEightMixedOwnerC4Clauses).toArray

def eightEightMixedOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses eightEightMixedOwnerDimacsClauses

set_option maxHeartbeats 0 in
theorem eightEightMixedOwners_size : eightEightMixedOwners.length = 48 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightMixedOwnerVariables_size :
    eightEightMixedOwnerVariables.length = 644 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightMixedOwnerDimacsClauses_size :
    eightEightMixedOwnerDimacsClauses.size = 87952 := by
  native_decide

end Erdos85
