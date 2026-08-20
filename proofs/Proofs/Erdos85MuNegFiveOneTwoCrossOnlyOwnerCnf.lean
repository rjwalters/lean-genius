import Proofs.Erdos85MuNegFiveCanonicalOwnerCnf

/-!
# Correct cross-only owner CNF for h512

At `(mu,k,r)=(-5,1,2)` every within-shore pair which could be an exterior
owner is a defect pair.  Thus the owner universe consists of the 64 cross
cells only.  This generator retains the checked cross profile and
intertwining blocks, but rebuilds all owner/hit/service/C4 indices over that
geometrically complete 64-owner universe.
-/

namespace Erdos85

open Std Sat

def muNegFiveOneTwoCrossOnlyOwnerAt (e : Nat) : EightEightOwner :=
  (muNegFiveZeroThreeCrossCandidates[e]?).getD (0, 8)

def muNegFiveOneTwoCrossOnlyOwnerContains (e v : Nat) : Bool :=
  let p := muNegFiveOneTwoCrossOnlyOwnerAt e
  p.1 == v || p.2 == v

def muNegFiveOneTwoCrossOnlyOwnerTargetContains (e v : Nat) : Bool :=
  let p := muNegFiveOneTwoCrossOnlyOwnerAt e
  !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v

def muNegFiveOneTwoCrossOnlyOwnerCompatible (e f : Nat) : Bool :=
  e != f &&
    muNegFiveOneTwoCrossOnlyOwnerTargetContains e
      (muNegFiveOneTwoCrossOnlyOwnerAt f).1 &&
    muNegFiveOneTwoCrossOnlyOwnerTargetContains e
      (muNegFiveOneTwoCrossOnlyOwnerAt f).2 &&
    muNegFiveOneTwoCrossOnlyOwnerTargetContains f
      (muNegFiveOneTwoCrossOnlyOwnerAt e).1 &&
    muNegFiveOneTwoCrossOnlyOwnerTargetContains f
      (muNegFiveOneTwoCrossOnlyOwnerAt e).2

def muNegFiveOneTwoCrossOnlyHitVariables : List (Nat × Nat) :=
  (List.range 64).flatMap fun e ↦
    ((List.range 64).filter fun f ↦
      e < f && muNegFiveOneTwoCrossOnlyOwnerCompatible e f).map fun f ↦ (e, f)

def muNegFiveOneTwoCrossOnlyActiveVariable? (e : Nat) : Option Nat :=
  (muNegFiveZeroThreeCrossCandidates.idxOf?
    (muNegFiveOneTwoCrossOnlyOwnerAt e)).map (· + 1)

def muNegFiveOneTwoCrossOnlyHitVariable? (e f : Nat) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (muNegFiveOneTwoCrossOnlyHitVariables.idxOf? p).map (· + 65)

def muNegFiveOneTwoCrossOnlyHitLiteral? (e f : Nat) : Option Int :=
  (muNegFiveOneTwoCrossOnlyHitVariable? e f).map Int.ofNat

def muNegFiveOneTwoCrossOnlyActiveGuard (e : Nat) : List Int :=
  match muNegFiveOneTwoCrossOnlyActiveVariable? e with
  | some a => [-Int.ofNat a]
  | none => []

def muNegFiveOneTwoCrossOnlyHitActivityClauses : List DimacsClause :=
  muNegFiveOneTwoCrossOnlyHitVariables.flatMap fun (e, f) ↦
    let h := Int.ofNat ((muNegFiveOneTwoCrossOnlyHitVariable? e f).getD 0)
    let ce := match muNegFiveOneTwoCrossOnlyActiveVariable? e with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    let cf := match muNegFiveOneTwoCrossOnlyActiveVariable? f with
      | some a => [[-h, Int.ofNat a]]
      | none => []
    ce ++ cf

def muNegFiveOneTwoCrossOnlyServiceVariables (e v : Nat) : List Int :=
  (List.range 64).filterMap fun f ↦
    if f != e && muNegFiveOneTwoCrossOnlyOwnerContains f v then
      muNegFiveOneTwoCrossOnlyHitLiteral? e f
    else none

def muNegFiveOneTwoCrossOnlyServiceClauses : List DimacsClause :=
  (List.range 64).flatMap fun e ↦
    (List.range 16).flatMap fun v ↦
      let p := muNegFiveOneTwoCrossOnlyOwnerAt e
      let xs := muNegFiveOneTwoCrossOnlyServiceVariables e v
      let guard := muNegFiveOneTwoCrossOnlyActiveGuard e
      if !eightEightHighCycleAdj p.1 v && !eightEightHighCycleAdj p.2 v then
        [guard ++ xs] ++ eightEightPairwiseNegativeClauses xs
      else xs.map fun x ↦ guard ++ [-x]

def muNegFiveOneTwoCrossOnlyOwnersIntersect (e f : Nat) : Bool :=
  let p := muNegFiveOneTwoCrossOnlyOwnerAt e
  muNegFiveOneTwoCrossOnlyOwnerContains f p.1 ||
    muNegFiveOneTwoCrossOnlyOwnerContains f p.2

def muNegFiveOneTwoCrossOnlyCommonCandidates (e f : Nat) : List Nat :=
  (List.range 64).filter fun k ↦ k != e && k != f &&
    (muNegFiveOneTwoCrossOnlyHitVariable? e k).isSome &&
    (muNegFiveOneTwoCrossOnlyHitVariable? f k).isSome

def muNegFiveOneTwoCrossOnlyNoCommonClauses (e f : Nat) : List DimacsClause :=
  (muNegFiveOneTwoCrossOnlyCommonCandidates e f).filterMap fun k ↦ do
    let x ← muNegFiveOneTwoCrossOnlyHitLiteral? e k
    let y ← muNegFiveOneTwoCrossOnlyHitLiteral? f k
    return [-x, -y]

def muNegFiveOneTwoCrossOnlyAtMostOneCommonClauses
    (e f : Nat) : List DimacsClause :=
  let ks := muNegFiveOneTwoCrossOnlyCommonCandidates e f
  ks.flatMap fun k ↦ (ks.filter fun l ↦ k < l).filterMap fun l ↦ do
    let xek ← muNegFiveOneTwoCrossOnlyHitLiteral? e k
    let xfk ← muNegFiveOneTwoCrossOnlyHitLiteral? f k
    let xel ← muNegFiveOneTwoCrossOnlyHitLiteral? e l
    let xfl ← muNegFiveOneTwoCrossOnlyHitLiteral? f l
    return [-xek, -xfk, -xel, -xfl]

def muNegFiveOneTwoCrossOnlyC4Clauses : List DimacsClause :=
  (List.range 64).flatMap fun e ↦
    ((List.range 64).filter fun f ↦ e < f).flatMap fun f ↦
      if muNegFiveOneTwoCrossOnlyOwnersIntersect e f then
        muNegFiveOneTwoCrossOnlyNoCommonClauses e f
      else muNegFiveOneTwoCrossOnlyAtMostOneCommonClauses e f

def muNegFiveOneTwoCrossOnlyOwnerDimacsClauses (sigma : Bool) :
    Array DimacsClause :=
  (muNegFiveCanonicalCrossDegreeClauses 6 4 sigma ++
    muNegFiveZeroThreeIntertwiningClauses ++
    muNegFiveOneTwoCrossOnlyHitActivityClauses ++
    muNegFiveOneTwoCrossOnlyServiceClauses ++
    muNegFiveOneTwoCrossOnlyC4Clauses).toArray

def muNegFiveOneTwoCrossOnlyOwnerSatCnf (sigma : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (muNegFiveOneTwoCrossOnlyOwnerDimacsClauses sigma)

set_option maxHeartbeats 0 in
theorem muNegFiveOneTwoCrossOnlyHitVariables_size :
    muNegFiveOneTwoCrossOnlyHitVariables.length = 1120 := by native_decide

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnlyHitVariables_size
