import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal

/-!
# Byte-exact DIMACS emitters for the seven small-high bases

The solver-side cube manifests consume external DIMACS files.  This module
reconstructs those files from the same live Lean definitions used by the final
LRAT consumers and proves that conversion of every emitted clause array is
definitionally the corresponding `CNF Nat` clause array.
-/

namespace Erdos85.SmallHighCnfEmit

open Erdos85 Std Sat

def threeFormula (masks : Array Nat) (geometry : Array DimacsClause) :
    Array DimacsClause :=
  orderFortyNineVariableFixedClauses (3 : Fin 50) masks ++
  geometry ++
  orderFortyNineC4Clauses ++
  (orderFortyNineDegreeBlocks 3).clauses ++
  orderFortyNineVariablePartitionClauses (3 : Fin 50) masks

def fiveFormula (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineVariableFixedClauses (5 : Fin 50) masks ++
  orderFortyNineC4Clauses ++
  (orderFortyNineDegreeBlocks 5).clauses ++
  orderFortyNineVariablePartitionClauses (5 : Fin 50) masks

theorem h3B1_clause_identity :
    dimacsFormulaToSatClauses
      (threeFormula orderFortyNineThreeHighDistOneNoCoincidenceMasks
        orderFortyNineThreeHighDistOneB1GeometryClauses) =
      orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf.clauses := by
  simp [threeFormula, orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf,
    dimacsFormulaToSatClauses]

theorem h3C1_clause_identity :
    dimacsFormulaToSatClauses
      (threeFormula orderFortyNineThreeHighDistOneNoCoincidenceMasks
        orderFortyNineThreeHighDistOneC1GeometryClauses) =
      orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf.clauses := by
  simp [threeFormula, orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf,
    dimacsFormulaToSatClauses]

theorem h3C2_clause_identity :
    dimacsFormulaToSatClauses
      (threeFormula orderFortyNineThreeHighDistOneC2Masks
        orderFortyNineThreeHighDistOneC2GeometryClauses) =
      orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf.clauses := by
  simp [threeFormula, orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf,
    dimacsFormulaToSatClauses]

theorem h3Dist2_clause_identity :
    dimacsFormulaToSatClauses
      (threeFormula orderFortyNineThreeHighDistTwoMasks
        orderFortyNineThreeHighDistTwoGeometryClauses) =
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf.clauses := by
  simp [threeFormula, orderFortyNineGeneratedThreeHighDistTwoScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf,
    dimacsFormulaToSatClauses]

theorem h5T0_clause_identity :
    dimacsFormulaToSatClauses (fiveFormula orderFortyNineFiveHighT0Masks) =
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT0Masks).clauses := by
  simp [fiveFormula, orderFortyNineGeneratedVariableHighSatCnf,
    dimacsFormulaToSatClauses]

theorem h5T1_clause_identity :
    dimacsFormulaToSatClauses (fiveFormula orderFortyNineFiveHighT1Masks) =
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT1Masks).clauses := by
  simp [fiveFormula, orderFortyNineGeneratedVariableHighSatCnf,
    dimacsFormulaToSatClauses]

theorem h5T2_clause_identity :
    dimacsFormulaToSatClauses (fiveFormula orderFortyNineFiveHighT2Masks) =
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT2Masks).clauses := by
  simp [fiveFormula, orderFortyNineGeneratedVariableHighSatCnf,
    dimacsFormulaToSatClauses]

def clauseLine (clause : DimacsClause) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

def emit (top : Nat) (clauses : Array DimacsClause) : IO Unit := do
  IO.print s!"p cnf {top} {clauses.size}\n"
  let mut chunk := ""
  for i in [0:clauses.size] do
    chunk := chunk ++ clauseLine clauses[i]! ++ "\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then
    IO.print chunk

def run (args : List String) : IO UInt32 := do
  match args with
  | ["h3_b1"] =>
      emit (orderFortyNineDegreeBlocks 3).top
        (threeFormula orderFortyNineThreeHighDistOneNoCoincidenceMasks
          orderFortyNineThreeHighDistOneB1GeometryClauses)
      pure 0
  | ["h3_c1"] =>
      emit (orderFortyNineDegreeBlocks 3).top
        (threeFormula orderFortyNineThreeHighDistOneNoCoincidenceMasks
          orderFortyNineThreeHighDistOneC1GeometryClauses)
      pure 0
  | ["h3_c2"] =>
      emit (orderFortyNineDegreeBlocks 3).top
        (threeFormula orderFortyNineThreeHighDistOneC2Masks
          orderFortyNineThreeHighDistOneC2GeometryClauses)
      pure 0
  | ["h3_dist2"] =>
      emit (orderFortyNineDegreeBlocks 3).top
        (threeFormula orderFortyNineThreeHighDistTwoMasks
          orderFortyNineThreeHighDistTwoGeometryClauses)
      pure 0
  | ["h5_t0"] =>
      emit (orderFortyNineDegreeBlocks 5).top
        (fiveFormula orderFortyNineFiveHighT0Masks)
      pure 0
  | ["h5_t1"] =>
      emit (orderFortyNineDegreeBlocks 5).top
        (fiveFormula orderFortyNineFiveHighT1Masks)
      pure 0
  | ["h5_t2"] =>
      emit (orderFortyNineDegreeBlocks 5).top
        (fiveFormula orderFortyNineFiveHighT2Masks)
      pure 0
  | _ =>
      IO.eprintln
        "usage: <program> {h3_b1|h3_c1|h3_c2|h3_dist2|h5_t0|h5_t1|h5_t2}"
      pure 2

end Erdos85.SmallHighCnfEmit

def main (args : List String) : IO UInt32 :=
  Erdos85.SmallHighCnfEmit.run args
