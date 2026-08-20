import Proofs.Erdos85MuNegOneOneFourOwnerCnf

/-!
# Owner CNFs for the μ=-3 `(0,5)` endpoint

The h305 endpoint uses the same sixteen-cycle model, mode-dependent
within-shore owner offsets, intertwining law, hit activity, service law, and
exterior C4 law as the closed h114 owner model.  Only the cross defect degree
changes.  Since an h305 row has exterior split `2+1`, its four same-sign cells
contain exactly two defect entries and its four opposite-sign cells contain
exactly three.
-/

namespace Erdos85

open Std Sat

/-- Exact-three encoding used on a four-element sign class: every pair is
positive (at most one false), and the all-negative clause excludes four true
entries. -/
def muNegThreeExactlyThree (lits : List Int) : List DimacsClause :=
  ((List.range lits.length).flatMap fun i =>
    ((List.range lits.length).filter fun j => i < j).map fun j =>
      [lits[i]!, lits[j]!]) ++ [lits.map (fun x => -x)]

def muNegThreeZeroFiveCrossRowClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    muNegOneExactlyTwo (((List.range 8).filter fun j =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun j =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegThreeExactlyThree (((List.range 8).filter fun j =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun j =>
        Int.ofNat (muNegOneDVar i j))

def muNegThreeZeroFiveCrossColClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun j =>
    muNegOneExactlyTwo (((List.range 8).filter fun i =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun i =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegThreeExactlyThree (((List.range 8).filter fun i =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun i =>
        Int.ofNat (muNegOneDVar i j))

/-- The h305 generator.  The shore flags select offsets one (cycle-entry-one
mode) or three (cycle-entry-zero mode); `σ` is the relative alternating-sign
phase. -/
def muNegThreeZeroFiveOwnerDimacsClauses (uTri vTri σ : Bool) :
    Array DimacsClause :=
  let pairs := muNegOneHitPairs uTri vTri
  (muNegThreeZeroFiveCrossRowClauses σ ++
    muNegThreeZeroFiveCrossColClauses σ ++
    muNegOneIntertwineClauses ++
    muNegOneHitActivityClauses uTri vTri pairs ++
    muNegOneServiceClauses uTri vTri pairs ++
    muNegOneC4Clauses uTri vTri pairs).toArray

def muNegThreeZeroFiveOwnerSatCnf (uTri vTri σ : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (muNegThreeZeroFiveOwnerDimacsClauses uTri vTri σ)

end Erdos85
