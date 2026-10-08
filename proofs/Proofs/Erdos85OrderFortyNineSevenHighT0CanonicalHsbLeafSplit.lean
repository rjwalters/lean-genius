import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeaves

/-! # Splitting one hard `hsb` leaf

A leaf CNF `cube ∧ hsb ∧ (positive row units)` that is too hard for one
solver run can itself be split along any list of blocking clauses: one
checked CNF per sub-leaf (the leaf CNF plus the negated literals of the
sub-leaf's blocking clause as units) and one checked sub-cover CNF (the leaf
CNF plus all blocking clauses) give the leaf's `…HsbLeafChecked`.  The
blocking clauses are arbitrary; only the checked sub-cover vouches for them.
Nothing else changes: `SevenHighT0CanonicalHsbEvidence` consumes the result.
-/

namespace Erdos85

open Std Sat

/-- The leaf CNF: `cube ∧ hsb ∧` positive units of the leaf's rows. -/
def orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat)) : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf depth edgeCount typeIndex ++
    cnfClauseNegUnits (SevenHighT0Hsb.clause rows)

/-- Certificate-facing proposition for one sub-leaf of a split leaf. -/
def SevenHighT0CanonicalHsbSubLeafChecked
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat))
    (c : CNF.Clause Nat) : Prop :=
  (orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf depth edgeCount typeIndex
    rows ++ cnfClauseNegUnits c).Unsat

/-- Certificate-facing proposition for the sub-cover of a split leaf. -/
def SevenHighT0CanonicalHsbSubCoverChecked
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat))
    (blocking : List (CNF.Clause Nat)) : Prop :=
  (orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf depth edgeCount typeIndex
    rows ++ cnfOfClauseList blocking).Unsat

/-- A split leaf with all sub-leaves checked and a checked sub-cover is a
checked leaf. -/
theorem sevenHighT0CanonicalHsbLeafChecked_of_split
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat))
    (blocking : List (CNF.Clause Nat))
    (hsub : ∀ c ∈ blocking,
      SevenHighT0CanonicalHsbSubLeafChecked depth edgeCount typeIndex rows c)
    (hcover : SevenHighT0CanonicalHsbSubCoverChecked
      depth edgeCount typeIndex rows blocking) :
    SevenHighT0CanonicalHsbLeafChecked depth edgeCount typeIndex rows :=
  cnf_unsat_of_blocking_clauses
    (orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf
      depth edgeCount typeIndex rows) blocking hsub hcover

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalHsbLeafChecked_of_split
