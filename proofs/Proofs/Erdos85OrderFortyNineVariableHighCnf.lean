import Proofs.Erdos85DimacsSatBridge

/-!
# Exact variable-high order-49 CNFs

This is the high-count-parametric version of the four production segments used
by the surviving `h = 3` and `h = 5` SAT instances (and by the existing
specialized `h = 7` development): fixed high incidences, all C4 clauses,
threaded exact-degree blocks, and the adjacency-partition clauses.
-/

namespace Erdos85

open Std Sat

/-- A high count small enough to split the 49 vertices into an initial high
segment and a remaining low segment. -/
abbrev OrderFortyNineHighCount := Fin 50

def orderFortyNineVariableHighVertex (h : OrderFortyNineHighCount)
    (w : Fin h.val) : Fin 49 :=
  ⟨w.val, by omega⟩

def orderFortyNineVariableLowVertex (h : OrderFortyNineHighCount)
    (y : Fin (49 - h.val)) : Fin 49 :=
  ⟨y.val + h.val, by omega⟩

def orderFortyNineVariableHighPairs (h : OrderFortyNineHighCount) :
    List (Fin h.val × Fin h.val) :=
  (List.finRange h.val).flatMap fun a =>
    ((List.finRange h.val).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineVariableHighHighUnitLiteral
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (a b : Fin h.val) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineVariableHighVertex h a)
    (orderFortyNineVariableHighVertex h b)
  if (orderFortyNineSupportMask masks
      (orderFortyNineVariableHighVertex h a)).getLsbD b.val then edge else -edge

def orderFortyNineVariableHighHighFixedClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) : Array DimacsClause :=
  (orderFortyNineVariableHighPairs h |>.map fun ab =>
    [orderFortyNineVariableHighHighUnitLiteral h masks ab.1 ab.2]).toArray

def orderFortyNineVariableSupportUnitLiteral
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (y : Fin (49 - h.val)) (w : Fin h.val) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineVariableLowVertex h y)
    (orderFortyNineVariableHighVertex h w)
  if (orderFortyNineSupportMask masks
      (orderFortyNineVariableLowVertex h y)).getLsbD w.val then edge else -edge

def orderFortyNineVariableHighLowFixedClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) : Array DimacsClause :=
  ((List.finRange (49 - h.val)).flatMap fun y =>
    (List.finRange h.val).map fun w =>
      [orderFortyNineVariableSupportUnitLiteral h masks y w]).toArray

def orderFortyNineVariableFixedClauses
  (h : OrderFortyNineHighCount) (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineVariableHighHighFixedClauses h masks ++
    orderFortyNineVariableHighLowFixedClauses h masks

def OrderFortyNineVariableHighMasksZero
    (h : OrderFortyNineHighCount) (masks : Array Nat) : Prop :=
  ∀ a w : Fin h.val,
    (orderFortyNineSupportMask masks
      (orderFortyNineVariableHighVertex h a)).getLsbD w.val = false

def orderFortyNineVariablePartitionNeighbors
    (h : OrderFortyNineHighCount) (masks : Array Nat) (w : Fin h.val) :
    List (Fin 49) :=
  ((List.finRange (49 - h.val)).map
      (orderFortyNineVariableLowVertex h)).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNineVariablePartitionClause
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (y : Fin (49 - h.val)) (w : Fin h.val) : DimacsClause :=
  ((orderFortyNineVariablePartitionNeighbors h masks w).filter fun x =>
      x ≠ orderFortyNineVariableLowVertex h y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineVariableLowVertex h y) x

def orderFortyNineVariablePartitionClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) : Array DimacsClause :=
  ((List.finRange (49 - h.val)).flatMap fun y =>
    (List.finRange h.val).map fun w =>
      orderFortyNineVariablePartitionClause h masks y w).toArray

/-- The exact production CNF at a given high count. -/
def orderFortyNineGeneratedVariableHighSatCnf
    (h : OrderFortyNineHighCount) (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineVariableFixedClauses h masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks h.val).clauses ++
    dimacsFormulaToSatClauses
      (orderFortyNineVariablePartitionClauses h masks)

theorem orderFortyNineVariableHighPairs_length_three :
    (orderFortyNineVariableHighPairs (3 : Fin 50)).length = 3 := by
  native_decide

theorem orderFortyNineVariableHighPairs_length_five :
    (orderFortyNineVariableHighPairs (5 : Fin 50)).length = 10 := by
  native_decide

theorem orderFortyNineVariableFixedClauses_size_three (masks : Array Nat) :
    (orderFortyNineVariableFixedClauses (3 : Fin 50) masks).size = 141 := by
  simp [orderFortyNineVariableFixedClauses,
    orderFortyNineVariableHighHighFixedClauses,
    orderFortyNineVariableHighLowFixedClauses]
  simpa using orderFortyNineVariableHighPairs_length_three

theorem orderFortyNineVariablePartitionClauses_size_three (masks : Array Nat) :
    (orderFortyNineVariablePartitionClauses (3 : Fin 50) masks).size = 138 := by
  simp [orderFortyNineVariablePartitionClauses]

theorem orderFortyNineVariableFixedClauses_size_five (masks : Array Nat) :
    (orderFortyNineVariableFixedClauses (5 : Fin 50) masks).size = 230 := by
  simp [orderFortyNineVariableFixedClauses,
    orderFortyNineVariableHighHighFixedClauses,
    orderFortyNineVariableHighLowFixedClauses]
  simpa using orderFortyNineVariableHighPairs_length_five

theorem orderFortyNineVariablePartitionClauses_size_five (masks : Array Nat) :
    (orderFortyNineVariablePartitionClauses (5 : Fin 50) masks).size = 220 := by
  simp [orderFortyNineVariablePartitionClauses]

theorem orderFortyNineDegreeBlocks_three_top :
    (orderFortyNineDegreeBlocks 3).top = 29500 := by native_decide

theorem orderFortyNineDegreeBlocks_five_top :
    (orderFortyNineDegreeBlocks 5).top = 29632 := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orderFortyNineGeneratedVariableHighSatCnf_clause_count_three
    (masks : Array Nat) :
    (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50) masks).clauses.size =
      1328183 := by
  simp [orderFortyNineGeneratedVariableHighSatCnf, dimacsFormulaToSatClauses,
    orderFortyNineVariableFixedClauses_size_three,
    orderFortyNineVariablePartitionClauses_size_three]
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orderFortyNineGeneratedVariableHighSatCnf_clause_count_five
    (masks : Array Nat) :
    (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) masks).clauses.size =
      1328618 := by
  simp [orderFortyNineGeneratedVariableHighSatCnf, dimacsFormulaToSatClauses,
    orderFortyNineVariableFixedClauses_size_five,
    orderFortyNineVariablePartitionClauses_size_five]
  native_decide

end Erdos85
