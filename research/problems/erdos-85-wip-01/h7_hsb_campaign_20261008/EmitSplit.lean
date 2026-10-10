import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeafSplit

/- Split-leaf byte identity (README section 9).

The two certificate-facing formulas of `…HsbLeafSplit.lean` are, as clause arrays (the theorems
below are `rfl`, checked when this file is run):

  sub-leaf  = cube ++ hsb ++ cnfClauseNegUnits (clause rows) ++ cnfClauseNegUnits c
  sub-cover = cube ++ hsb ++ cnfClauseNegUnits (clause rows) ++ cnfOfClauseList blocking

`cube ++ hsb` is already byte-identical to the campaign inputs (receipts/base_cube_lean_identity.json
and the hsb identity receipt). This program prints the remaining TAILS from the Lean definitions,
in Lean clause order, Std.Sat variable `v` written as DIMACS `v + 1` (as `EmitCube.lean`):

    lake env lean --run EmitSplit.lean ROWS C_0 C_1 ... C_{m-1}

ROWS = the leaf's rows as outside-vertex lists, `/`-separated, comma inside (e.g. `27,32,36,39/…`);
C_k = blocking clause k as comma-separated DIMACS literals. Output: `c tail leaf` + the leaf units,
then `c tail subleaf k` + the units of sub-leaf k for every k, then `c tail subcover` + the blocking
clauses; check_split_identity.py compares each segment with h7_common. -/

open Erdos85 Std Sat

theorem subLeaf_clauses (d e t : Nat) (rows : List (List Nat)) (c : CNF.Clause Nat) :
    (orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf d e t rows ++ cnfClauseNegUnits c).clauses =
      (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf d e t).clauses ++
        (cnfClauseNegUnits (SevenHighT0Hsb.clause rows)).clauses ++ (cnfClauseNegUnits c).clauses := rfl

theorem subCover_clauses (d e t : Nat) (rows : List (List Nat)) (bs : List (CNF.Clause Nat)) :
    (orderFortyNineSevenHighT0CanonicalHsbLeafSatCnf d e t rows ++ cnfOfClauseList bs).clauses =
      (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf d e t).clauses ++
        (cnfClauseNegUnits (SevenHighT0Hsb.clause rows)).clauses ++ (cnfOfClauseList bs).clauses := rfl

def litStr (l : Nat × Bool) : String :=
  (if l.2 then "" else "-") ++ toString (l.1 + 1)

def emitClauses (cnf : CNF Nat) : IO Unit := do
  for c in cnf.clauses do
    IO.print (String.intercalate " " (c.map litStr) ++ " 0\n")

/-- DIMACS literal `±(v + 1)` as the Std.Sat literal `(v, sign)`. -/
def parseLit (s : String) : Nat × Bool :=
  let i := s.toInt!
  (i.natAbs - 1, decide (0 < i))

def parseClause (s : String) : CNF.Clause Nat :=
  (s.splitOn ",").map parseLit

def parseRows (s : String) : List (List Nat) :=
  (s.splitOn "/").map fun r => (r.splitOn ",").map String.toNat!

def main (args : List String) : IO UInt32 := do
  match args with
  | rowsSpec :: cs =>
      let rows := parseRows rowsSpec
      let bs := cs.map parseClause
      IO.print "c tail leaf\n"
      emitClauses (cnfClauseNegUnits (SevenHighT0Hsb.clause rows))
      let mut k := 0
      for c in bs do
        IO.print s!"c tail subleaf {k}\n"
        emitClauses (cnfClauseNegUnits c)
        k := k + 1
      IO.print "c tail subcover\n"
      emitClauses (cnfOfClauseList bs)
      pure 0
  | [] => do IO.eprintln "usage: ROWS C_0 C_1 ..."; pure 2
