import Proofs.Erdos85EightEightLowOwnerCnf

/-!
# Finite owner-tiling CNF for the mixed six-plus-ten model

The C6 shore has the three antipodal exterior pairs.  The all-triangle C10
shore has exterior-pair offsets `±1` and `5`.
Cross-shore exterior pairs join opposite parity.  The service and C4 clause
families are identical to the checked low-model encoding.
-/

namespace Erdos85

open Std Sat

def sixTenSameShore (a b : Nat) : Bool := (a < 6) == (b < 6)

def sixTenCycleAdj (a b : Nat) : Bool :=
  sixTenSameShore a b &&
    (if a < 6 then
      ((a + 1) % 6 == b % 6) || ((b + 1) % 6 == a % 6)
    else
      ((((a - 6) + 1) % 10 == (b - 6) % 10) ||
        (((b - 6) + 1) % 10 == (a - 6) % 10)))

def sixTenMixedOwnerPair (a b : Nat) : Bool :=
  a < b && (if sixTenSameShore a b then
    if a < 6 then
      (b + 6 - a) % 6 == 3
    else
      ((b + 10 - a) % 10 == 1) ||
        ((b + 10 - a) % 10 == 5) ||
        ((b + 10 - a) % 10 == 9)
  else
    a % 2 != (b - 6) % 2)

def sixTenMixedOwners : List EightEightOwner :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => sixTenMixedOwnerPair a b).map
      fun b => (a, b)

def sixTenMixedOwnerAt (e : Nat) : EightEightOwner :=
  (sixTenMixedOwners[e]?).getD (0, 0)

def sixTenMixedOwnerContains (e v : Nat) : Bool :=
  let p := sixTenMixedOwnerAt e
  p.1 == v || p.2 == v

def sixTenMixedOwnerTargetContains (e v : Nat) : Bool :=
  let p := sixTenMixedOwnerAt e
  !sixTenCycleAdj p.1 v && !sixTenCycleAdj p.2 v

def sixTenMixedOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    sixTenMixedOwnerTargetContains e (sixTenMixedOwnerAt f).1 &&
    sixTenMixedOwnerTargetContains e (sixTenMixedOwnerAt f).2 &&
    sixTenMixedOwnerTargetContains f (sixTenMixedOwnerAt e).1 &&
    sixTenMixedOwnerTargetContains f (sixTenMixedOwnerAt e).2

def sixTenMixedOwnerVariables : List (Nat × Nat) :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f =>
      e < f && sixTenMixedOwnerCompatible e f).map fun f => (e, f)

def sixTenMixedOwnerVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (sixTenMixedOwnerVariables.idxOf? p).map (· + 1)

def sixTenMixedOwnerLiteral? (e f : Nat) : Option Int :=
  (sixTenMixedOwnerVariable? e f).map Int.ofNat

def sixTenMixedOwnerServiceVariables (e v : Nat) : List Int :=
  (List.range 48).filterMap fun f =>
    if f != e && sixTenMixedOwnerContains f v then
      sixTenMixedOwnerLiteral? e f
    else none

def sixTenMixedOwnerServiceClauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := sixTenMixedOwnerAt e
      if !sixTenCycleAdj p.1 v && !sixTenCycleAdj p.2 v then
        let xs := sixTenMixedOwnerServiceVariables e v
        [xs] ++ eightEightPairwiseNegativeClauses xs
      else []

def sixTenMixedOwnersIntersect (e f : Nat) : Bool :=
  let p := sixTenMixedOwnerAt e
  sixTenMixedOwnerContains f p.1 ||
    sixTenMixedOwnerContains f p.2

def sixTenMixedOwnerCommonCandidates (e f : Nat) : List Nat :=
  (List.range 48).filter fun k => k != e && k != f &&
    (sixTenMixedOwnerVariable? e k).isSome &&
    (sixTenMixedOwnerVariable? f k).isSome

def sixTenMixedOwnerNoCommonClauses (e f : Nat) : List DimacsClause :=
  (sixTenMixedOwnerCommonCandidates e f).filterMap fun k => do
    let x ← sixTenMixedOwnerLiteral? e k
    let y ← sixTenMixedOwnerLiteral? f k
    return [-x, -y]

def sixTenMixedOwnerAtMostOneCommonClauses
    (e f : Nat) : List DimacsClause :=
  let ks := sixTenMixedOwnerCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← sixTenMixedOwnerLiteral? e k
    let xfk ← sixTenMixedOwnerLiteral? f k
    let xel ← sixTenMixedOwnerLiteral? e l
    let xfl ← sixTenMixedOwnerLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def sixTenMixedOwnerC4Clauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f).flatMap fun f =>
      if sixTenMixedOwnersIntersect e f then
        sixTenMixedOwnerNoCommonClauses e f
      else
        sixTenMixedOwnerAtMostOneCommonClauses e f

def sixTenMixedOwnerDimacsClauses : Array DimacsClause :=
  (sixTenMixedOwnerServiceClauses ++
    sixTenMixedOwnerC4Clauses).toArray

def sixTenMixedOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses sixTenMixedOwnerDimacsClauses

set_option maxHeartbeats 0 in
theorem sixTenMixedOwners_size : sixTenMixedOwners.length = 48 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sixTenMixedOwnerVariables_size :
    sixTenMixedOwnerVariables.length = 640 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sixTenMixedOwnerDimacsClauses_size :
    sixTenMixedOwnerDimacsClauses.size = 86186 := by
  native_decide

end Erdos85
