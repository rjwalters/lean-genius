import Proofs.Erdos85EightEightHighOwnerCnf

/-!
# Variable-cross owner CNF for the `mu = -5`, `(k,r) = (0,3)` endpoint

The two internal shores are all triangle-free.  Their fixed exterior owners
are the eight antipodal pairs.  Across the shores, the defect block has
degree three with signed split `1+2`, so its exterior complement has degree
five with signed split `3+2`.  The Boolean variable block below records that
cross exterior relation for either relative sign phase.
-/

namespace Erdos85

open Std Sat

def muNegFiveZeroThreeFixedOwnerPair (a b : Nat) : Bool :=
  a < b && eightEightHighSameShore a b &&
    ((b + 8 - a) % 8 == 4)

def muNegFiveZeroThreeCrossCandidatePair (a b : Nat) : Bool :=
  a < 8 && 8 ≤ b && b < 16

def muNegFiveZeroThreeCandidatePair (a b : Nat) : Bool :=
  muNegFiveZeroThreeFixedOwnerPair a b ||
    muNegFiveZeroThreeCrossCandidatePair a b

def muNegFiveZeroThreeCandidates : List EightEightOwner :=
  (List.range 16).flatMap fun a ↦
    ((List.range 16).filter fun b ↦
      muNegFiveZeroThreeCandidatePair a b).map fun b ↦ (a, b)

def muNegFiveZeroThreeCrossCandidates : List EightEightOwner :=
  muNegFiveZeroThreeCandidates.filter fun p ↦ p.1 < 8 && 8 ≤ p.2

def muNegFiveZeroThreeCrossIndex? (x y : Nat) : Option Nat :=
  if x < 8 && y < 8 then
    let p : EightEightOwner := (x, 8 + y)
    (muNegFiveZeroThreeCrossCandidates.idxOf? p).map (· + 1)
  else none

def muNegFiveZeroThreeCrossFiber (left : Bool) (z : Nat) : List Nat :=
  (List.range 8).filterMap fun w ↦
    let x := if left then z else w
    let y := if left then w else z
    muNegFiveZeroThreeCrossIndex? x y

/-- `σ=false` means the two coordinate-zero signs agree; `σ=true`
means they are opposite. -/
def muNegFiveZeroThreeSameSign (sigma : Bool) (x y : Nat) : Bool :=
  ((x % 2 == y % 2) != sigma)

def muNegFiveZeroThreeBit (mask place : Nat) : Bool :=
  ((mask / (2 ^ place)) % 2) == 1

def muNegFiveZeroThreeMaskClause (vars : List Nat) (mask : Nat) : DimacsClause :=
  (vars.zipIdx.map fun (v, i) ↦
    if muNegFiveZeroThreeBit mask i then -Int.ofNat v else Int.ofNat v)

def muNegFiveZeroThreeFiberAllowed
    (sigma left : Bool) (z mask : Nat) : Bool :=
  let bits := (List.range 8).map fun w ↦ muNegFiveZeroThreeBit mask w
  let total := (bits.map Bool.toNat).sum
  let same := ((List.range 8).filter fun w ↦
    let x := if left then z else w
    let y := if left then w else z
    muNegFiveZeroThreeSameSign sigma x y).foldl
      (fun n w ↦ n + (muNegFiveZeroThreeBit mask w).toNat) 0
  total == 5 && same == 3

/-- Truth-table encoding of row/column degree five with signed split `3+2`.
Each forbidden eight-bit fiber contributes the clause excluding exactly that
assignment. -/
def muNegFiveZeroThreeCrossDegreeClauses (sigma : Bool) : List DimacsClause :=
  (List.range 2).flatMap fun side ↦
    (List.range 8).flatMap fun z ↦
      let left := side == 0
      let vars := muNegFiveZeroThreeCrossFiber left z
      (List.range 256).filterMap fun mask ↦
        if muNegFiveZeroThreeFiberAllowed sigma left z mask then none
        else some (muNegFiveZeroThreeMaskClause vars mask)

/-- The exterior cross block commutes with the two cycle adjacency
operators, just as its defect complement does. -/
def muNegFiveZeroThreeIntertwiningClauses : List DimacsClause :=
  (List.range 8).flatMap fun x ↦
    (List.range 8).flatMap fun y ↦
      let vars? := [
        muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y,
        muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y,
        muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8),
        muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8)]
      match vars?.mapM id with
      | none => []
      | some vars =>
          (List.range 16).filterMap fun mask ↦
            let b0 := muNegFiveZeroThreeBit mask 3
            let b1 := muNegFiveZeroThreeBit mask 2
            let b2 := muNegFiveZeroThreeBit mask 1
            let b3 := muNegFiveZeroThreeBit mask 0
            if b0.toNat + b1.toNat != b2.toNat + b3.toNat then
              some <| (vars.zip [b0, b1, b2, b3]).map fun (v, bit) ↦
                if bit then -Int.ofNat v else Int.ofNat v
            else none

def muNegFiveZeroThreeOwnerAt (e : Nat) : EightEightOwner :=
  (muNegFiveZeroThreeCandidates[e]?).getD (0, 0)

def muNegFiveZeroThreeOwnerContains (e v : Nat) : Bool :=
  let p := muNegFiveZeroThreeOwnerAt e
  p.1 == v || p.2 == v

def muNegFiveZeroThreeOwnerTargetContains (e v : Nat) : Bool :=
  let p := muNegFiveZeroThreeOwnerAt e
  !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v

def muNegFiveZeroThreeOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    muNegFiveZeroThreeOwnerTargetContains e (muNegFiveZeroThreeOwnerAt f).1 &&
    muNegFiveZeroThreeOwnerTargetContains e (muNegFiveZeroThreeOwnerAt f).2 &&
    muNegFiveZeroThreeOwnerTargetContains f (muNegFiveZeroThreeOwnerAt e).1 &&
    muNegFiveZeroThreeOwnerTargetContains f (muNegFiveZeroThreeOwnerAt e).2

def muNegFiveZeroThreeHitVariables : List (Nat × Nat) :=
  (List.range 72).flatMap fun e ↦
    ((List.range 72).filter fun f ↦
      e < f && muNegFiveZeroThreeOwnerCompatible e f).map fun f ↦ (e, f)

def muNegFiveZeroThreeActiveVariable? (e : Nat) : Option Nat :=
  let p := muNegFiveZeroThreeOwnerAt e
  if p.1 < 8 && 8 ≤ p.2 then
    (muNegFiveZeroThreeCrossCandidates.idxOf? p).map (· + 1)
  else none

def muNegFiveZeroThreeHitVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (muNegFiveZeroThreeHitVariables.idxOf? p).map (· + 65)

def muNegFiveZeroThreeHitLiteral? (e f : Nat) : Option Int :=
  (muNegFiveZeroThreeHitVariable? e f).map Int.ofNat

def muNegFiveZeroThreeActiveGuard (e : Nat) : List Int :=
  match muNegFiveZeroThreeActiveVariable? e with
  | some a => [-Int.ofNat a]
  | none => []

def muNegFiveZeroThreeHitActivityClauses : List DimacsClause :=
  muNegFiveZeroThreeHitVariables.flatMap fun (e, f) ↦
    let h := Int.ofNat ((muNegFiveZeroThreeHitVariable? e f).getD 0)
    let ce := match muNegFiveZeroThreeActiveVariable? e with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    let cf := match muNegFiveZeroThreeActiveVariable? f with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    ce ++ cf

def muNegFiveZeroThreeServiceVariables (e v : Nat) : List Int :=
  (List.range 72).filterMap fun f ↦
    if f != e && muNegFiveZeroThreeOwnerContains f v then
      muNegFiveZeroThreeHitLiteral? e f
    else none

def muNegFiveZeroThreeServiceClauses : List DimacsClause :=
  (List.range 72).flatMap fun e ↦
    (List.range 16).flatMap fun v ↦
      let p := muNegFiveZeroThreeOwnerAt e
      let xs := muNegFiveZeroThreeServiceVariables e v
      let guard := muNegFiveZeroThreeActiveGuard e
      if !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v then
        [guard ++ xs] ++ eightEightPairwiseNegativeClauses xs
      else
        xs.map fun x ↦ guard ++ [-x]

def muNegFiveZeroThreeOwnersIntersect (e f : Nat) : Bool :=
  let p := muNegFiveZeroThreeOwnerAt e
  muNegFiveZeroThreeOwnerContains f p.1 ||
    muNegFiveZeroThreeOwnerContains f p.2

def muNegFiveZeroThreeCommonCandidates (e f : Nat) : List Nat :=
  (List.range 72).filter fun k ↦ k != e && k != f &&
    (muNegFiveZeroThreeHitVariable? e k).isSome &&
    (muNegFiveZeroThreeHitVariable? f k).isSome

def muNegFiveZeroThreeNoCommonClauses (e f : Nat) : List DimacsClause :=
  (muNegFiveZeroThreeCommonCandidates e f).filterMap fun k ↦ do
    let x ← muNegFiveZeroThreeHitLiteral? e k
    let y ← muNegFiveZeroThreeHitLiteral? f k
    return [-x, -y]

def muNegFiveZeroThreeAtMostOneCommonClauses
    (e f : Nat) : List DimacsClause :=
  let ks := muNegFiveZeroThreeCommonCandidates e f
  ks.flatMap fun k ↦ (ks.filter fun l ↦ k < l).filterMap fun l ↦ do
    let xek ← muNegFiveZeroThreeHitLiteral? e k
    let xfk ← muNegFiveZeroThreeHitLiteral? f k
    let xel ← muNegFiveZeroThreeHitLiteral? e l
    let xfl ← muNegFiveZeroThreeHitLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def muNegFiveZeroThreeC4Clauses : List DimacsClause :=
  (List.range 72).flatMap fun e ↦
    ((List.range 72).filter fun f ↦ e < f).flatMap fun f ↦
      if muNegFiveZeroThreeOwnersIntersect e f then
        muNegFiveZeroThreeNoCommonClauses e f
      else muNegFiveZeroThreeAtMostOneCommonClauses e f

def muNegFiveZeroThreeStructuralClauses (sigma : Bool) : Array DimacsClause :=
  (muNegFiveZeroThreeCrossDegreeClauses sigma ++
    muNegFiveZeroThreeIntertwiningClauses).toArray

def muNegFiveZeroThreeDimacsClauses (sigma : Bool) : Array DimacsClause :=
  (muNegFiveZeroThreeCrossDegreeClauses sigma ++
    muNegFiveZeroThreeIntertwiningClauses ++
    muNegFiveZeroThreeHitActivityClauses ++
    muNegFiveZeroThreeServiceClauses ++
    muNegFiveZeroThreeC4Clauses).toArray

def muNegFiveZeroThreeSatCnf (sigma : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses (muNegFiveZeroThreeDimacsClauses sigma)

set_option maxHeartbeats 0 in
theorem muNegFiveZeroThreeCandidates_size :
    muNegFiveZeroThreeCandidates.length = 72 := by native_decide

set_option maxHeartbeats 0 in
theorem muNegFiveZeroThreeCrossCandidates_size :
    muNegFiveZeroThreeCrossCandidates.length = 64 := by native_decide

set_option maxHeartbeats 0 in
theorem muNegFiveZeroThreeCrossFibers_size :
    ∀ left z, z < 8 → (muNegFiveZeroThreeCrossFiber left z).length = 8 := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegFiveZeroThreeStructuralClauses_size :
    ∀ sigma, (muNegFiveZeroThreeStructuralClauses sigma).size = 4352 := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeCandidates_size
#print axioms Erdos85.muNegFiveZeroThreeCrossCandidates_size
#print axioms Erdos85.muNegFiveZeroThreeCrossFibers_size
#print axioms Erdos85.muNegFiveZeroThreeStructuralClauses_size
