import Proofs.Erdos85OneHighFamilyCnfSatisfaction

/-!
# Table-pinned one-high CNFs

The wholesale family CNF existentially chooses every inter-branch miss count.
The successful sweep instead fixes those counts to one symmetric miss table.
This file defines that exact certificate-facing extension: its prefix is the
already certified PURE family formula, followed by one sequential-counter
equality for every non-mate unordered pair of branches.
-/

namespace Erdos85

/-- An encoder miss table.  Only entries with `c < j` and `j != c ^^^ 1`
are read by the pinned generator. -/
abbrev OneHighMissTable := Nat → Nat → Nat

/-- Non-mate unordered branch pairs, in the same nested-loop order as the
fleet worker (`c = 0..7`, then `j = 0..7`). -/
def oneHighFamilyTablePairs : List (Nat × Nat) :=
  (List.range 8).flatMap fun c =>
    (List.range 8).filterMap fun j =>
      if c < j ∧ j != (c ^^^ 1) then some (c, j) else none

theorem oneHighFamilyTablePairs_size : oneHighFamilyTablePairs.length = 24 := by
  native_decide

/-- Collect the miss atoms in branch `c` pointing at branch `j`.  The
matched-vertex filter is precisely the worker's `if x in matched` list. -/
def oneHighFamilyTableMissVars (a c j : Nat)
    (st : OneHighFamilyGenState) : Array Int × OneHighFamilyGenState :=
  (oneHighFamilyBlockVertices c).foldl (fun (vars, st) w =>
    if oneHighFamilyVertexMatched a w then
      let (id, st) := oneHighFamilyAtomId (.miss w j) st
      (vars.push (id : Int), st)
    else (vars, st)) (#[], st)

theorem oneHighFamilyIdsSound_tableMissVars
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a c j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyTableMissVars a c j st).2 := by
  unfold oneHighFamilyTableMissVars
  apply oneHighFamilyIdsSound_foldlAccum _ _ #[] h
  intro w vars st hw
  simp only
  split
  · exact oneHighFamilyIdsSound_atomId hw (.miss w j)
  · exact hw

/-- Append the exact-cardinality pin for one table entry. -/
def oneHighFamilyTablePairStep (a : Nat) (table : OneHighMissTable)
    (pair : Nat × Nat) (st : OneHighFamilyGenState) :
    OneHighFamilyGenState :=
  let (vars, st) := oneHighFamilyTableMissVars a pair.1 pair.2 st
  oneHighFamilyEqualsBlock vars (table pair.1 pair.2) st

theorem oneHighFamilyIdsSound_tablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyIdsSound (oneHighFamilyTablePairStep a table pair st) := by
  simp only [oneHighFamilyTablePairStep]
  exact oneHighFamilyIdsSound_equalsBlock
    (oneHighFamilyIdsSound_tableMissVars h a pair.1 pair.2) _ _

/-- The exact per-table CNF consumed by an orbit-sweep certificate. -/
def oneHighFamilyTableClauses (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyTablePairs
    (oneHighFamilyTablePairStep a table) (oneHighFamilyPureClauses a)

theorem oneHighFamilyIdsSound_tableClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyTableClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_pureClauses a)
    (fun pair st h => oneHighFamilyIdsSound_tablePairStep h a table pair)

def oneHighFamilyTableSatCnf (a : Nat) (table : OneHighMissTable) :
    Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (oneHighFamilyTableClauses a table).clauses

end Erdos85
