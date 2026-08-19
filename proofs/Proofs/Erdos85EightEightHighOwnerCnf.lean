import Proofs.Erdos85EightEightLowOwnerCnf

/-!
# Variable-cross owner CNF for the high eight-plus-eight parameter

At quotient parameter six, both internal exterior-pair blocks have offsets
`±1, ±3`.  The cross exterior block is not assumed to have a preselected
circulant support: its 32 opposite-parity candidates are Boolean variables,
constrained to have row and column degree two and to intertwine the two C8
adjacency operators.  The remaining clauses are the exact owner-service and
common-neighbor constraints.  Thus one checked CNF covers every cross block,
including the antipodal support class.
-/

namespace Erdos85

open Std Sat

def eightEightHighSameShore (a b : Nat) : Bool := (a < 8) == (b < 8)

def eightEightHighCycleAdj (a b : Nat) : Bool :=
  eightEightHighSameShore a b &&
    (((a % 8 + 1) % 8 == b % 8) || ((b % 8 + 1) % 8 == a % 8))

def eightEightHighFixedOwnerPair (a b : Nat) : Bool :=
  a < b && eightEightHighSameShore a b &&
    (let d := (b + 8 - a) % 8; d == 1 || d == 3 || d == 5 || d == 7)

def eightEightHighCrossCandidatePair (a b : Nat) : Bool :=
  a < 8 && 8 ≤ b && b < 16 && a % 2 != (b - 8) % 2

def eightEightHighCandidatePair (a b : Nat) : Bool :=
  eightEightHighFixedOwnerPair a b || eightEightHighCrossCandidatePair a b

def eightEightHighCandidates : List EightEightOwner :=
  (List.range 16).flatMap fun a =>
    ((List.range 16).filter fun b => eightEightHighCandidatePair a b).map
      fun b => (a, b)

def eightEightHighCrossCandidates : List EightEightOwner :=
  eightEightHighCandidates.filter fun p => p.1 < 8 && 8 ≤ p.2

def eightEightHighOwnerAt (e : Nat) : EightEightOwner :=
  (eightEightHighCandidates[e]?).getD (0, 0)

def eightEightHighOwnerContains (e v : Nat) : Bool :=
  let p := eightEightHighOwnerAt e
  p.1 == v || p.2 == v

def eightEightHighOwnerTargetContains (e v : Nat) : Bool :=
  let p := eightEightHighOwnerAt e
  !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v

def eightEightHighOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    eightEightHighOwnerTargetContains e (eightEightHighOwnerAt f).1 &&
    eightEightHighOwnerTargetContains e (eightEightHighOwnerAt f).2 &&
    eightEightHighOwnerTargetContains f (eightEightHighOwnerAt e).1 &&
    eightEightHighOwnerTargetContains f (eightEightHighOwnerAt e).2

def eightEightHighHitVariables : List (Nat × Nat) :=
  (List.range 64).flatMap fun e =>
    ((List.range 64).filter fun f =>
      e < f && eightEightHighOwnerCompatible e f).map fun f => (e, f)

def eightEightHighActiveVariable? (e : Nat) : Option Nat :=
  let p := eightEightHighOwnerAt e
  if p.1 < 8 && 8 ≤ p.2 then
    (eightEightHighCrossCandidates.idxOf? p).map (· + 1)
  else none

def eightEightHighHitVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (eightEightHighHitVariables.idxOf? p).map (· + 33)

def eightEightHighHitLiteral? (e f : Nat) : Option Int :=
  (eightEightHighHitVariable? e f).map Int.ofNat

def eightEightHighActiveGuard (e : Nat) : List Int :=
  match eightEightHighActiveVariable? e with
  | some a => [-Int.ofNat a]
  | none => []

def eightEightHighCrossIndex? (x y : Nat) : Option Nat :=
  if x < 8 && y < 8 && x % 2 != y % 2 then
    let p : EightEightOwner := (x, 8 + y)
    (eightEightHighCrossCandidates.idxOf? p).map (· + 1)
  else none

def eightEightHighCrossFiber (left : Bool) (z : Nat) : List Int :=
  (List.range 8).filterMap fun w =>
    let x := if left == true then z else w
    let y := if left == true then w else z
    (eightEightHighCrossIndex? x y).map Int.ofNat

def eightEightHighCrossDegreeClauses : List DimacsClause :=
  (List.range 2).flatMap fun side =>
    (List.range 8).flatMap fun z =>
      let xs := eightEightHighCrossFiber (side == 0) z
      xs.flatMap fun a =>
        (xs.filter fun b => a < b).flatMap fun b =>
          (xs.filter fun c => b < c).flatMap fun c =>
            [[a, b, c], [-a, -b, -c]]

def eightEightHighBit (mask place : Nat) : Bool :=
  ((mask / (2 ^ place)) % 2) == 1

def eightEightHighIntertwiningClauses : List DimacsClause :=
  (List.range 8).flatMap fun x =>
    (List.range 8).flatMap fun y =>
      let vars? := [
        eightEightHighCrossIndex? ((x + 7) % 8) y,
        eightEightHighCrossIndex? ((x + 1) % 8) y,
        eightEightHighCrossIndex? x ((y + 1) % 8),
        eightEightHighCrossIndex? x ((y + 7) % 8)]
      match vars?.mapM id with
      | none => []
      | some vars =>
          (List.range 16).filterMap fun mask =>
            let b0 := eightEightHighBit mask 3
            let b1 := eightEightHighBit mask 2
            let b2 := eightEightHighBit mask 1
            let b3 := eightEightHighBit mask 0
            if b0.toNat + b1.toNat != b2.toNat + b3.toNat then
              some <| (vars.zip [b0, b1, b2, b3]).map fun (v, bit) =>
                if bit then -Int.ofNat v else Int.ofNat v
            else none

def eightEightHighHitActivityClauses : List DimacsClause :=
  eightEightHighHitVariables.flatMap fun (e, f) =>
    let h := Int.ofNat ((eightEightHighHitVariable? e f).getD 0)
    let ce := match eightEightHighActiveVariable? e with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    let cf := match eightEightHighActiveVariable? f with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    ce ++ cf

def eightEightHighServiceVariables (e v : Nat) : List Int :=
  (List.range 64).filterMap fun f =>
    if f != e && eightEightHighOwnerContains f v then
      eightEightHighHitLiteral? e f
    else none

def eightEightHighServiceClauses : List DimacsClause :=
  (List.range 64).flatMap fun e =>
    (List.range 16).flatMap fun v =>
      let p := eightEightHighOwnerAt e
      let xs := eightEightHighServiceVariables e v
      let guard := eightEightHighActiveGuard e
      if !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v then
        [guard ++ xs] ++ eightEightPairwiseNegativeClauses xs
      else
        xs.map fun x => guard ++ [-x]

def eightEightHighOwnersIntersect (e f : Nat) : Bool :=
  let p := eightEightHighOwnerAt e
  eightEightHighOwnerContains f p.1 || eightEightHighOwnerContains f p.2

def eightEightHighCommonCandidates (e f : Nat) : List Nat :=
  (List.range 64).filter fun k => k != e && k != f &&
    (eightEightHighHitVariable? e k).isSome &&
    (eightEightHighHitVariable? f k).isSome

def eightEightHighNoCommonClauses (e f : Nat) : List DimacsClause :=
  (eightEightHighCommonCandidates e f).filterMap fun k => do
    let x ← eightEightHighHitLiteral? e k
    let y ← eightEightHighHitLiteral? f k
    return [-x, -y]

def eightEightHighAtMostOneCommonClauses (e f : Nat) : List DimacsClause :=
  let ks := eightEightHighCommonCandidates e f
  ks.flatMap fun k => (ks.filter fun l => k < l).filterMap fun l => do
    let xek ← eightEightHighHitLiteral? e k
    let xfk ← eightEightHighHitLiteral? f k
    let xel ← eightEightHighHitLiteral? e l
    let xfl ← eightEightHighHitLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def eightEightHighC4Clauses : List DimacsClause :=
  (List.range 64).flatMap fun e =>
    ((List.range 64).filter fun f => e < f).flatMap fun f =>
      if eightEightHighOwnersIntersect e f then
        eightEightHighNoCommonClauses e f
      else
        eightEightHighAtMostOneCommonClauses e f

def eightEightHighDimacsClauses : Array DimacsClause :=
  (eightEightHighCrossDegreeClauses ++
    eightEightHighIntertwiningClauses ++
    eightEightHighHitActivityClauses ++
    eightEightHighServiceClauses ++
    eightEightHighC4Clauses).toArray

def eightEightHighOwnerSatCnf : CNF Nat where
  clauses := dimacsFormulaToSatClauses eightEightHighDimacsClauses

set_option maxHeartbeats 0 in
theorem eightEightHighCandidates_size : eightEightHighCandidates.length = 64 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightHighCrossCandidates_size :
    eightEightHighCrossCandidates.length = 32 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightHighHitVariables_size :
    eightEightHighHitVariables.length = 1128 := by
  native_decide

set_option maxHeartbeats 0 in
theorem eightEightHighDimacsClauses_size :
    eightEightHighDimacsClauses.size = 259472 := by
  native_decide

end Erdos85
