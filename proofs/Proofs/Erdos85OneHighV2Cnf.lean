import Proofs.Erdos85OneHighOrbitCnf

/-!
# Exact fleet-v2 one-high generator

The durable orbit certificates were produced by `sweep_worker.py` with
`arm:v2`.  Its clause order is not the PURE-family order: upper table pins
precede lex, and the reverse-direction F1 pins follow lex.  This file starts
a separate byte-exact transcription rather than attempting to reuse proofs
against a merely equisatisfiable formula.
-/

namespace Erdos85

/-- Worker-v2 through its first table pass:
base through miss definitions, then `c < j` exact miss-count blocks. -/
def oneHighFamilyV2UpperTableClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyTablePairs
    (oneHighFamilyTablePairStep a table)
    (oneHighFamilyMissDefinitionClauses a)

theorem oneHighFamilyIdsSound_v2UpperTableClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2UpperTableClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_missDefinitionClauses a)
    (fun pair st h => oneHighFamilyIdsSound_tablePairStep h a table pair)

/-- The worker's lex segment, now applied after upper table counters. -/
def oneHighFamilyV2LexClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) (oneHighFamilyLexBlockStep a)
    (oneHighFamilyV2UpperTableClauses a table)

theorem oneHighFamilyIdsSound_v2LexClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2LexClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2UpperTableClauses a table)
    (fun c st h => oneHighFamilyIdsSound_lexBlockStep h a c)

/-- Reverse-direction non-mate branch pairs in worker nested-loop order. -/
def oneHighFamilyV2LowerTablePairs : List (Nat × Nat) :=
  (List.range 8).flatMap fun c =>
    (List.range 8).filterMap fun j =>
      if j < c ∧ j != (c ^^^ 1) then some (c, j) else none

theorem oneHighFamilyV2LowerTablePairs_size :
    oneHighFamilyV2LowerTablePairs.length = 24 := by
  native_decide

/-- F1 reverse pin.  The table is stored on unordered coordinates, hence the
worker's `m_of(c,j)` at `j<c` reads `table j c`. -/
def oneHighFamilyV2LowerTablePairStep
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (vars, st) := oneHighFamilyTableMissVars a pair.1 pair.2 st
  oneHighFamilyEqualsBlock vars (table pair.2 pair.1) st

theorem oneHighFamilyIdsSound_v2LowerTablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2LowerTablePairStep a table pair st) := by
  simp only [oneHighFamilyV2LowerTablePairStep]
  exact oneHighFamilyIdsSound_equalsBlock
    (oneHighFamilyIdsSound_tableMissVars h a pair.1 pair.2) _ _

/-- Exact worker-v2 prefix through F1 (both directed table pin families). -/
def oneHighFamilyV2F1Clauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyV2LowerTablePairs
    (oneHighFamilyV2LowerTablePairStep a table)
    (oneHighFamilyV2LexClauses a table)

theorem oneHighFamilyIdsSound_v2F1Clauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2F1Clauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2LexClauses a table)
    (fun pair st h =>
      oneHighFamilyIdsSound_v2LowerTablePairStep h a table pair)

end Erdos85
