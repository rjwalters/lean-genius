import Proofs.Erdos85DimacsSatBridge

/-!
# Finite owner-tiling CNF for the both-all-TF 6+10 model

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The exact finite terminal attached to the graph model in
`Erdos85SizeTwoEigenlineSixTenAllTfExteriorModel` (squad-pinned model,
msg 12747; graph-facing package `…sixTen_allTf_exteriorPair_model`).
The sixteen internal vertices are numbered short C6 shore `0..5` then
long C10 shore `6..15`; the eigenline sign is the coordinate parity on
each shore (ids chosen so sign is plain parity).  The forty-eight owner
pairs are the exterior-pair edges: the three C6 antipodes, the long
offsets `{±3, 5}`, and all thirty opposite-sign cross pairs.  Every
owner pair is non-adjacent, so the served twelve-set of an owner is
exactly the complement of its endpoints' cycle neighbourhoods, with the
endpoints themselves included.
-/

namespace Erdos85

open Std Sat

def sixTenShoreLong (a : Nat) : Bool := 6 ≤ a

def sixTenAllTfCycleAdj (a b : Nat) : Bool :=
  if sixTenShoreLong a != sixTenShoreLong b then false
  else if sixTenShoreLong a then
    ((a - 6 + 1) % 10 == (b - 6) % 10) || ((b - 6 + 1) % 10 == (a - 6) % 10)
  else
    ((a + 1) % 6 == b % 6) || ((b + 1) % 6 == a % 6)

def sixTenAllTfOwnerPair (a b : Nat) : Bool :=
  a < b &&
    (if sixTenShoreLong a != sixTenShoreLong b then
      a % 2 != b % 2
    else if sixTenShoreLong a then
      let d := (b - a) % 10
      d == 3 || d == 5 || d == 7
    else
      b - a == 3)

def sixTenAllTfOwners : List (Nat × Nat) :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => sixTenAllTfOwnerPair a b).map fun b => (a, b)

def sixTenAllTfOwnerAt (e : Nat) : Nat × Nat :=
  (sixTenAllTfOwners[e]?).getD (0, 0)

def sixTenAllTfOwnerContains (e v : Nat) : Bool :=
  let p := sixTenAllTfOwnerAt e
  p.1 == v || p.2 == v

def sixTenAllTfOwnerTargetContains (e v : Nat) : Bool :=
  let p := sixTenAllTfOwnerAt e
  !sixTenAllTfCycleAdj p.1 v && !sixTenAllTfCycleAdj p.2 v

def sixTenAllTfOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    sixTenAllTfOwnerTargetContains e (sixTenAllTfOwnerAt f).1 &&
    sixTenAllTfOwnerTargetContains e (sixTenAllTfOwnerAt f).2 &&
    sixTenAllTfOwnerTargetContains f (sixTenAllTfOwnerAt e).1 &&
    sixTenAllTfOwnerTargetContains f (sixTenAllTfOwnerAt e).2

def sixTenAllTfOwnerVariables : List (Nat × Nat) :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f && sixTenAllTfOwnerCompatible e f).map
      fun f => (e, f)

def sixTenAllTfOwnerVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (sixTenAllTfOwnerVariables.idxOf? p).map (· + 1)

def sixTenAllTfOwnerLiteral? (e f : Nat) : Option Int :=
  (sixTenAllTfOwnerVariable? e f).map Int.ofNat

def sixTenAllTfOwnerServiceVariables (e v : Nat) : List Int :=
  (List.range 48).filterMap fun f =>
    if f != e && sixTenAllTfOwnerContains f v then
      sixTenAllTfOwnerLiteral? e f
    else none

def sixTenPairwiseNegativeClauses (xs : List Int) : List DimacsClause :=
  xs.flatMap fun x => (xs.filter fun y => x < y).map fun y => [-x, -y]

def sixTenAllTfOwnerServiceClauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := sixTenAllTfOwnerAt e
      if !sixTenAllTfCycleAdj p.1 v && !sixTenAllTfCycleAdj p.2 v then
        let xs := sixTenAllTfOwnerServiceVariables e v
        [xs] ++ sixTenPairwiseNegativeClauses xs
      else []

def sixTenAllTfOwnersIntersect (e f : Nat) : Bool :=
  let p := sixTenAllTfOwnerAt e
  sixTenAllTfOwnerContains f p.1 || sixTenAllTfOwnerContains f p.2

def sixTenAllTfOwnerCommonCandidates (e f : Nat) : List Nat :=
  (List.range 48).filter fun k => k != e && k != f &&
    (sixTenAllTfOwnerVariable? e k).isSome &&
    (sixTenAllTfOwnerVariable? f k).isSome

def sixTenAllTfOwnerNoCommonClauses (e f : Nat) : List DimacsClause :=
  (sixTenAllTfOwnerCommonCandidates e f).filterMap fun k => do
    let x ← sixTenAllTfOwnerLiteral? e k
    let y ← sixTenAllTfOwnerLiteral? f k
    return [-x, -y]

def sixTenAllTfOwnerAtMostOneCommonClauses (e f : Nat) : List DimacsClause :=
  let ks := sixTenAllTfOwnerCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← sixTenAllTfOwnerLiteral? e k
    let xfk ← sixTenAllTfOwnerLiteral? f k
    let xel ← sixTenAllTfOwnerLiteral? e l
    let xfl ← sixTenAllTfOwnerLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def sixTenAllTfOwnerC4Clauses : List DimacsClause :=
  (List.range 48).flatMap fun e =>
    ((List.range 48).filter fun f => e < f).flatMap fun f =>
      if sixTenAllTfOwnersIntersect e f then
        sixTenAllTfOwnerNoCommonClauses e f
      else
        sixTenAllTfOwnerAtMostOneCommonClauses e f

def sixTenAllTfOwnerDimacsClauses : Array DimacsClause :=
  (sixTenAllTfOwnerServiceClauses ++ sixTenAllTfOwnerC4Clauses).toArray

def sixTenAllTfOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses sixTenAllTfOwnerDimacsClauses

set_option maxHeartbeats 0 in
theorem sixTenAllTfOwners_size : sixTenAllTfOwners.length = 48 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sixTenAllTfOwnerVariables_size :
    sixTenAllTfOwnerVariables.length = 640 := by
  native_decide

set_option maxHeartbeats 0 in
theorem sixTenAllTfOwnerDimacsClauses_size :
    sixTenAllTfOwnerDimacsClauses.size = 86606 := by
  native_decide

end Erdos85
