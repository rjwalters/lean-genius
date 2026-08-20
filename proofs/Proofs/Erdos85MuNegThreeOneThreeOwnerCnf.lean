import Proofs.Erdos85MuNegOneOneFourOwnerCnf

/-!
# Owner CNF for the μ=-3 `(1,3)` endpoint

Node: outline F.3 negative-lane endpoint h313 (squad msgs 14299/14306).

Both h313 shores are all-cycle-entries-one with same-sign defect only
at the antipode, so the within-shore exterior owner universe is the
offset-three family — exactly the `(−1,1,4)` TF/TF owner table.  The
only difference from the checked h114 CNF is the cross-defect profile:
each sign class of four carries exactly one same-sign and exactly two
opposite-sign defect cells per row and column (exterior `5 = 3+2`).
All other clause families (intertwining, hit activity, guarded
service, exterior C4) are reused verbatim over the same owner and
hit-pair tables.
-/

namespace Erdos85

open Std Sat

/-- Python-order exactly-one: the at-least-one clause, then negated
pairs in combination order. -/
def muNegThreeOneThreeExactlyOne (lits : List Int) : List DimacsClause :=
  [lits] ++
  ((List.range lits.length).flatMap fun i =>
    ((List.range lits.length).filter fun j => i < j).map fun j =>
      [-lits[i]!, -lits[j]!])

/-- Cross-defect rows: exactly one same-sign and exactly two
opposite-sign defect cells. -/
def muNegThreeOneThreeCrossRowClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    muNegThreeOneThreeExactlyOne (((List.range 8).filter fun j =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun j =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegOneExactlyTwo (((List.range 8).filter fun j =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun j =>
        Int.ofNat (muNegOneDVar i j))

/-- Cross-defect columns: exactly one same-sign and exactly two
opposite-sign defect cells. -/
def muNegThreeOneThreeCrossColClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun j =>
    muNegThreeOneThreeExactlyOne (((List.range 8).filter fun i =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun i =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegOneExactlyTwo (((List.range 8).filter fun i =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun i =>
        Int.ofNat (muNegOneDVar i j))

/-- The complete h313 owner formula over the TF/TF owner universe. -/
def muNegThreeOneThreeOwnerDimacsClauses (σ : Bool) :
    Array DimacsClause :=
  let pairs := muNegOneHitPairs false false
  (muNegThreeOneThreeCrossRowClauses σ ++
    muNegThreeOneThreeCrossColClauses σ ++
    muNegOneIntertwineClauses ++
    muNegOneHitActivityClauses false false pairs ++
    muNegOneServiceClauses false false pairs ++
    muNegOneC4Clauses false false pairs).toArray

def muNegThreeOneThreeOwnerSatCnf (σ : Bool) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (muNegThreeOneThreeOwnerDimacsClauses σ)

end Erdos85
