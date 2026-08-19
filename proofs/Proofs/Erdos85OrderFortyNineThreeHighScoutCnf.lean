import Proofs.Erdos85OrderFortyNineThreeHighScoutMasks

/-!
# Exact normalized CNFs for the surviving three-high scouts

The historical generators add unit clauses fixing the induced perfect
matching in each high neighborhood.  The distance-two scout additionally
fixes the complete low neighborhood of the unique triple-support vertex.
After these units, both files use the standard universal C4, exact-degree,
and high-neighborhood partition segments.
-/

namespace Erdos85

open Std Sat

def orderFortyNinePinnedMatchingClauses
    (vertices : List (Fin 49)) (matching : List (Fin 49 × Fin 49)) :
    Array DimacsClause :=
  (orderFortyNineStrictPairs vertices |>.map fun ab =>
    [if ab ∈ matching then orderFortyNineEdgeLiteral ab.1 ab.2
      else -orderFortyNineEdgeLiteral ab.1 ab.2]).toArray

def orderFortyNineThreeHighDistTwoMatchingClauses : Array DimacsClause :=
  orderFortyNinePinnedMatchingClauses
      [3, 4, 5, 6, 7, 8, 9, 10]
      [(3, 4), (5, 6), (7, 8), (9, 10)] ++
    orderFortyNinePinnedMatchingClauses
      [3, 11, 14, 15, 16, 17, 18, 19]
      [(3, 11), (14, 15), (16, 17), (18, 19)] ++
    orderFortyNinePinnedMatchingClauses
      [3, 12, 20, 21, 22, 23, 24, 25]
      [(3, 12), (20, 21), (22, 23), (24, 25)]

def orderFortyNineThreeHighDistTwoRootEmptyClauses : Array DimacsClause :=
  ([13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
      38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48].map fun z =>
    [if z = 13 then orderFortyNineEdgeLiteral 3 z
      else -orderFortyNineEdgeLiteral 3 z]).toArray

def orderFortyNineThreeHighDistTwoGeometryClauses : Array DimacsClause :=
  orderFortyNineThreeHighDistTwoMatchingClauses ++
    orderFortyNineThreeHighDistTwoRootEmptyClauses

def orderFortyNineThreeHighDistOneC2GeometryClauses : Array DimacsClause :=
  orderFortyNinePinnedMatchingClauses
      [3, 4, 5, 6, 7, 8, 9, 10]
      [(3, 4), (5, 6), (7, 8), (9, 10)] ++
    orderFortyNinePinnedMatchingClauses
      [3, 12, 13, 14, 15, 16, 17, 25]
      [(3, 25), (12, 13), (14, 15), (16, 17)] ++
    orderFortyNinePinnedMatchingClauses
      [5, 18, 19, 20, 21, 22, 23, 25]
      [(5, 18), (19, 25), (20, 21), (22, 23)]

def orderFortyNineThreeHighDistOneB1GeometryClauses : Array DimacsClause :=
  orderFortyNinePinnedMatchingClauses
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 4), (6, 7), (8, 9), (10, 11)] ++
    orderFortyNinePinnedMatchingClauses
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)] ++
    orderFortyNinePinnedMatchingClauses
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)]

def orderFortyNineThreeHighDistOneC1GeometryClauses : Array DimacsClause :=
  orderFortyNinePinnedMatchingClauses
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 6), (4, 7), (8, 9), (10, 11)] ++
    orderFortyNinePinnedMatchingClauses
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)] ++
    orderFortyNinePinnedMatchingClauses
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)]

def orderFortyNineGeneratedThreeHighScoutCnf
    (masks : Array Nat) (geometry : Array DimacsClause) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses
      (orderFortyNineVariableFixedClauses (3 : Fin 50) masks) ++
    dimacsFormulaToSatClauses geometry ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks 3).clauses ++
    dimacsFormulaToSatClauses
      (orderFortyNineVariablePartitionClauses (3 : Fin 50) masks)

def orderFortyNineGeneratedThreeHighDistTwoScoutCnf : CNF Nat :=
  orderFortyNineGeneratedThreeHighScoutCnf
    orderFortyNineThreeHighDistTwoMasks
    orderFortyNineThreeHighDistTwoGeometryClauses

def orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf : CNF Nat :=
  orderFortyNineGeneratedThreeHighScoutCnf
    orderFortyNineThreeHighDistOneC2Masks
    orderFortyNineThreeHighDistOneC2GeometryClauses

def orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf : CNF Nat :=
  orderFortyNineGeneratedThreeHighScoutCnf
    orderFortyNineThreeHighDistOneNoCoincidenceMasks
    orderFortyNineThreeHighDistOneB1GeometryClauses

def orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf : CNF Nat :=
  orderFortyNineGeneratedThreeHighScoutCnf
    orderFortyNineThreeHighDistOneNoCoincidenceMasks
    orderFortyNineThreeHighDistOneC1GeometryClauses

theorem orderFortyNineThreeHighDistTwoMatchingClauses_size :
    orderFortyNineThreeHighDistTwoMatchingClauses.size = 84 := by native_decide

theorem orderFortyNineThreeHighDistTwoRootEmptyClauses_size :
    orderFortyNineThreeHighDistTwoRootEmptyClauses.size = 24 := by native_decide

theorem orderFortyNineThreeHighDistTwoGeometryClauses_size :
    orderFortyNineThreeHighDistTwoGeometryClauses.size = 108 := by native_decide

theorem orderFortyNineThreeHighDistOneC2GeometryClauses_size :
    orderFortyNineThreeHighDistOneC2GeometryClauses.size = 84 := by native_decide

theorem orderFortyNineThreeHighDistOneB1GeometryClauses_size :
    orderFortyNineThreeHighDistOneB1GeometryClauses.size = 84 := by
  native_decide

theorem orderFortyNineThreeHighDistOneC1GeometryClauses_size :
    orderFortyNineThreeHighDistOneC1GeometryClauses.size = 84 := by
  native_decide

theorem orderFortyNineGeneratedThreeHighDistTwoScoutCnf_clause_count :
    orderFortyNineGeneratedThreeHighDistTwoScoutCnf.clauses.size = 1328291 := by
  have hbase := orderFortyNineGeneratedVariableHighSatCnf_clause_count_three
    orderFortyNineThreeHighDistTwoMasks
  simp only [orderFortyNineGeneratedVariableHighSatCnf,
    Array.size_append] at hbase
  simp only [orderFortyNineGeneratedThreeHighDistTwoScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf, Array.size_append]
  have hgeom : (dimacsFormulaToSatClauses
      orderFortyNineThreeHighDistTwoGeometryClauses).size = 108 := by
    simp [dimacsFormulaToSatClauses,
      orderFortyNineThreeHighDistTwoGeometryClauses_size]
  rw [hgeom]
  norm_num at hbase ⊢
  omega

theorem orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf_clause_count :
    orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf.clauses.size =
      1328267 := by
  have hbase := orderFortyNineGeneratedVariableHighSatCnf_clause_count_three
    orderFortyNineThreeHighDistOneC2Masks
  simp only [orderFortyNineGeneratedVariableHighSatCnf,
    Array.size_append] at hbase
  simp only [orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf, Array.size_append]
  have hgeom : (dimacsFormulaToSatClauses
      orderFortyNineThreeHighDistOneC2GeometryClauses).size = 84 := by
    simp [dimacsFormulaToSatClauses,
      orderFortyNineThreeHighDistOneC2GeometryClauses_size]
  rw [hgeom]
  norm_num at hbase ⊢
  omega

theorem orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf_clause_count :
    orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf.clauses.size =
      1328267 := by
  have hbase := orderFortyNineGeneratedVariableHighSatCnf_clause_count_three
    orderFortyNineThreeHighDistOneNoCoincidenceMasks
  simp only [orderFortyNineGeneratedVariableHighSatCnf,
    Array.size_append] at hbase
  simp only [orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf, Array.size_append]
  have hgeom : (dimacsFormulaToSatClauses
      orderFortyNineThreeHighDistOneB1GeometryClauses).size = 84 := by
    simp [dimacsFormulaToSatClauses,
      orderFortyNineThreeHighDistOneB1GeometryClauses_size]
  rw [hgeom]
  norm_num at hbase ⊢
  omega

theorem orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf_clause_count :
    orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf.clauses.size =
      1328267 := by
  have hbase := orderFortyNineGeneratedVariableHighSatCnf_clause_count_three
    orderFortyNineThreeHighDistOneNoCoincidenceMasks
  simp only [orderFortyNineGeneratedVariableHighSatCnf,
    Array.size_append] at hbase
  simp only [orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf,
    orderFortyNineGeneratedThreeHighScoutCnf, Array.size_append]
  have hgeom : (dimacsFormulaToSatClauses
      orderFortyNineThreeHighDistOneC1GeometryClauses).size = 84 := by
    simp [dimacsFormulaToSatClauses,
      orderFortyNineThreeHighDistOneC1GeometryClauses_size]
  rw [hgeom]
  norm_num at hbase ⊢
  omega

end Erdos85
