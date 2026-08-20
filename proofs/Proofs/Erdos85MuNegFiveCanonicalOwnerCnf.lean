import Proofs.Erdos85MuNegFiveZeroThreeOwnerCnf

/-!
# Owner CNFs for the remaining canonical `mu = -5` endpoints

The h503, h504, and h512 leaves have identical owner universe, activity,
service, C4, and intertwining clauses.  Only the exterior cross-fiber profile
changes.  This generator reuses the already-audited h503 geometry and exposes
the h504 `(total,same)=(4,3)` and h512 `(6,4)` formulas.
-/

namespace Erdos85

open Std Sat

def muNegFiveCanonicalFiberAllowed
    (total same : Nat) (sigma left : Bool) (z mask : Nat) : Bool :=
  let bits := (List.range 8).map fun w ↦ muNegFiveZeroThreeBit mask w
  let actualTotal := (bits.map Bool.toNat).sum
  let actualSame := ((List.range 8).filter fun w ↦
    let x := if left then z else w
    let y := if left then w else z
    muNegFiveZeroThreeSameSign sigma x y).foldl
      (fun n w ↦ n + (muNegFiveZeroThreeBit mask w).toNat) 0
  actualTotal == total && actualSame == same

def muNegFiveCanonicalCrossDegreeClauses
    (total same : Nat) (sigma : Bool) : List DimacsClause :=
  (List.range 2).flatMap fun side ↦
    (List.range 8).flatMap fun z ↦
      let left := side == 0
      let vars := muNegFiveZeroThreeCrossFiber left z
      (List.range 256).filterMap fun mask ↦
        if muNegFiveCanonicalFiberAllowed total same sigma left z mask then none
        else some (muNegFiveZeroThreeMaskClause vars mask)

def muNegFiveCanonicalOwnerDimacsClauses
    (total same : Nat) (sigma : Bool) : Array DimacsClause :=
  (muNegFiveCanonicalCrossDegreeClauses total same sigma ++
    muNegFiveZeroThreeIntertwiningClauses ++
    muNegFiveZeroThreeHitActivityClauses ++
    muNegFiveZeroThreeServiceClauses ++
    muNegFiveZeroThreeC4Clauses).toArray

def muNegFiveZeroFourOwnerDimacsClauses (sigma : Bool) : Array DimacsClause :=
  muNegFiveCanonicalOwnerDimacsClauses 4 3 sigma

def muNegFiveOneTwoOwnerDimacsClauses (sigma : Bool) : Array DimacsClause :=
  muNegFiveCanonicalOwnerDimacsClauses 6 4 sigma

def muNegFiveZeroFourOwnerSatCnf (sigma : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses (muNegFiveZeroFourOwnerDimacsClauses sigma)

def muNegFiveOneTwoOwnerSatCnf (sigma : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses (muNegFiveOneTwoOwnerDimacsClauses sigma)

end Erdos85
