import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85OrderFortyNineSevenHighProfileMasks

/-!
# Exact h=7 order-49 CNF

This is the Lean counterpart of `generate_h7_canonical_cnfs.py`: vertices
`0..6` are high, vertices `7..48` are low, degree rows are generated with
parameter seven, and the final partition segment has `42 * 7` clauses.
-/

namespace Erdos85

open Std Sat

def orderFortyNineH7HighVertex (w : Fin 7) : Fin 49 := ⟨w.val, by omega⟩

def orderFortyNineH7LowVertex (y : Fin 42) : Fin 49 := ⟨y.val + 7, by omega⟩

def orderFortyNineH7HighPairs : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun a =>
    ((List.finRange 7).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineH7HighHighFixedClauses : Array DimacsClause :=
  (orderFortyNineH7HighPairs.map fun ab =>
    [-orderFortyNineEdgeLiteral
      (orderFortyNineH7HighVertex ab.1) (orderFortyNineH7HighVertex ab.2)]).toArray

def orderFortyNineH7SupportUnitLiteral
    (masks : Array Nat) (y : Fin 42) (w : Fin 7) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineH7LowVertex y) (orderFortyNineH7HighVertex w)
  if (orderFortyNineSupportMask masks (orderFortyNineH7LowVertex y)).getLsbD w.val
    then edge else -edge

def orderFortyNineH7HighLowFixedClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 42).flatMap fun y =>
    (List.finRange 7).map fun w =>
      [orderFortyNineH7SupportUnitLiteral masks y w]).toArray

def orderFortyNineH7FixedClauses (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineH7HighHighFixedClauses ++
    orderFortyNineH7HighLowFixedClauses masks

def OrderFortyNineH7HighMasksZero (masks : Array Nat) : Prop :=
  ∀ a w : Fin 7,
    (orderFortyNineSupportMask masks (orderFortyNineH7HighVertex a)).getLsbD
      w.val = false

def orderFortyNineH7PartitionNeighbors (masks : Array Nat) (w : Fin 7) :
    List (Fin 49) :=
  ((List.finRange 42).map orderFortyNineH7LowVertex).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNineH7PartitionClause
    (masks : Array Nat) (y : Fin 42) (w : Fin 7) : DimacsClause :=
  ((orderFortyNineH7PartitionNeighbors masks w).filter fun x =>
      x ≠ orderFortyNineH7LowVertex y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineH7LowVertex y) x

def orderFortyNineH7PartitionClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 42).flatMap fun y =>
    (List.finRange 7).map fun w =>
      orderFortyNineH7PartitionClause masks y w).toArray

def orderFortyNineGeneratedH7SatCnf (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineH7FixedClauses masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks 7).clauses ++
    dimacsFormulaToSatClauses (orderFortyNineH7PartitionClauses masks)

theorem orderFortyNineH7HighPairs_length :
    orderFortyNineH7HighPairs.length = 21 := by native_decide

theorem orderFortyNineH7FixedClauses_size (masks : Array Nat) :
    (orderFortyNineH7FixedClauses masks).size = 315 := by
  simp [orderFortyNineH7FixedClauses, orderFortyNineH7HighHighFixedClauses,
    orderFortyNineH7HighLowFixedClauses, orderFortyNineH7HighPairs_length]

theorem orderFortyNineH7PartitionClauses_size (masks : Array Nat) :
    (orderFortyNineH7PartitionClauses masks).size = 294 := by
  simp [orderFortyNineH7PartitionClauses]

theorem representativeMasks_h7_high_zero (blocks index : Nat) :
    OrderFortyNineH7HighMasksZero
      (OrderFortyNineSevenHighCensus.representativeMasks blocks index) := by
  intro a w
  have h := OrderFortyNineSevenHighCensus.representativeMasks_high_zero
    blocks index a
  have hw := congrArg (fun mask : BitVec 9 => mask.getLsbD w.val) h
  simpa [orderFortyNineH7HighVertex] using hw

theorem orderFortyNineDegreeBlocks_seven_top :
    (orderFortyNineDegreeBlocks 7).top = 29764 := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orderFortyNineGeneratedH7SatCnf_clause_count (masks : Array Nat) :
    (orderFortyNineGeneratedH7SatCnf masks).clauses.size = 1329041 := by
  simp [orderFortyNineGeneratedH7SatCnf, dimacsFormulaToSatClauses,
    orderFortyNineH7FixedClauses_size,
    orderFortyNineH7PartitionClauses_size]
  native_decide

end Erdos85
