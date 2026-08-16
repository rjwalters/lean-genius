import Proofs.Erdos85DimacsSatBridge

/-!
# Canonical order-49 CNFs at an arbitrary high count

The original checked generator was specialized to nine high vertices, and
the later seven-high campaign introduced a second specialization.  The
three- and five-high survivor CNFs share the same four-segment base with a
different high prefix (the pinned three-high shards append additional unit
clauses).  This module factors out that base parameter so those five
remaining cells have a Lean-native certificate target.
-/

namespace Erdos85

open Std Sat

/-- A high count strictly below 50, packaged so all generated vertex labels
are definitionally in `Fin 49`. -/
abbrev OrderFortyNineHighCount := Fin 50

def orderFortyNineCanonicalHighVertex (h : OrderFortyNineHighCount)
    (w : Fin h.val) : Fin 49 :=
  ⟨w.val, by omega⟩

def orderFortyNineCanonicalLowVertex (h : OrderFortyNineHighCount)
    (y : Fin (49 - h.val)) : Fin 49 :=
  ⟨y.val + h.val, by omega⟩

def orderFortyNineCanonicalHighPairs (h : OrderFortyNineHighCount) :
    List (Fin h.val × Fin h.val) :=
  (List.finRange h.val).flatMap fun a =>
    ((List.finRange h.val).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineCanonicalHighHighFixedClauses
    (h : OrderFortyNineHighCount) : Array DimacsClause :=
  ((orderFortyNineCanonicalHighPairs h).map fun ab =>
    [-orderFortyNineEdgeLiteral
      (orderFortyNineCanonicalHighVertex h ab.1)
      (orderFortyNineCanonicalHighVertex h ab.2)]).toArray

def orderFortyNineCanonicalSupportUnitLiteral
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (y : Fin (49 - h.val)) (w : Fin h.val) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineCanonicalLowVertex h y)
    (orderFortyNineCanonicalHighVertex h w)
  if (orderFortyNineSupportMask masks
      (orderFortyNineCanonicalLowVertex h y)).getLsbD w.val
    then edge else -edge

def orderFortyNineCanonicalHighLowFixedClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange (49 - h.val)).flatMap fun y =>
    (List.finRange h.val).map fun w =>
      [orderFortyNineCanonicalSupportUnitLiteral h masks y w]).toArray

def orderFortyNineCanonicalFixedClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    Array DimacsClause :=
  orderFortyNineCanonicalHighHighFixedClauses h ++
    orderFortyNineCanonicalHighLowFixedClauses h masks

def orderFortyNineCanonicalPartitionNeighbors
    (h : OrderFortyNineHighCount) (masks : Array Nat) (w : Fin h.val) :
    List (Fin 49) :=
  ((List.finRange (49 - h.val)).map
      (orderFortyNineCanonicalLowVertex h)).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNineCanonicalPartitionClause
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (y : Fin (49 - h.val)) (w : Fin h.val) : DimacsClause :=
  ((orderFortyNineCanonicalPartitionNeighbors h masks w).filter fun x =>
      x ≠ orderFortyNineCanonicalLowVertex h y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineCanonicalLowVertex h y) x

def orderFortyNineCanonicalPartitionClauses
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange (49 - h.val)).flatMap fun y =>
    (List.finRange h.val).map fun w =>
      orderFortyNineCanonicalPartitionClause h masks y w).toArray

/-- The common exact CNF used by the odd high-count strata. -/
def orderFortyNineGeneratedCanonicalSatCnf
    (h : OrderFortyNineHighCount) (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineCanonicalFixedClauses h masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks h.val).clauses ++
    dimacsFormulaToSatClauses
      (orderFortyNineCanonicalPartitionClauses h masks)

theorem orderFortyNineCanonicalFixedClauses_three_size (masks : Array Nat) :
    (orderFortyNineCanonicalFixedClauses 3 masks).size = 141 := by
  simp [orderFortyNineCanonicalFixedClauses,
    orderFortyNineCanonicalHighHighFixedClauses,
    orderFortyNineCanonicalHighLowFixedClauses,
    orderFortyNineCanonicalHighPairs]
  native_decide

theorem orderFortyNineCanonicalFixedClauses_five_size (masks : Array Nat) :
    (orderFortyNineCanonicalFixedClauses 5 masks).size = 230 := by
  simp [orderFortyNineCanonicalFixedClauses,
    orderFortyNineCanonicalHighHighFixedClauses,
    orderFortyNineCanonicalHighLowFixedClauses,
    orderFortyNineCanonicalHighPairs]
  native_decide

theorem orderFortyNineCanonicalFixedClauses_seven_size (masks : Array Nat) :
    (orderFortyNineCanonicalFixedClauses 7 masks).size = 315 := by
  simp [orderFortyNineCanonicalFixedClauses,
    orderFortyNineCanonicalHighHighFixedClauses,
    orderFortyNineCanonicalHighLowFixedClauses,
    orderFortyNineCanonicalHighPairs]
  native_decide

theorem orderFortyNineCanonicalPartitionClauses_three_size
    (masks : Array Nat) :
    (orderFortyNineCanonicalPartitionClauses 3 masks).size = 138 := by
  simp [orderFortyNineCanonicalPartitionClauses]

theorem orderFortyNineCanonicalPartitionClauses_five_size
    (masks : Array Nat) :
    (orderFortyNineCanonicalPartitionClauses 5 masks).size = 220 := by
  simp [orderFortyNineCanonicalPartitionClauses]

theorem orderFortyNineCanonicalPartitionClauses_seven_size
    (masks : Array Nat) :
    (orderFortyNineCanonicalPartitionClauses 7 masks).size = 294 := by
  simp [orderFortyNineCanonicalPartitionClauses]

set_option maxHeartbeats 0 in
theorem orderFortyNineDegreeBlocks_three_clauses_size :
    (orderFortyNineDegreeBlocks 3).clauses.size = 56648 := by
  native_decide

set_option maxHeartbeats 0 in
theorem orderFortyNineDegreeBlocks_five_clauses_size :
    (orderFortyNineDegreeBlocks 5).clauses.size = 56912 := by
  native_decide

set_option maxHeartbeats 0 in
theorem orderFortyNineDegreeBlocks_seven_clauses_size :
    (orderFortyNineDegreeBlocks 7).clauses.size = 57176 := by
  native_decide

theorem orderFortyNineDegreeBlocks_three_top :
    (orderFortyNineDegreeBlocks 3).top = 29500 := by
  native_decide

theorem orderFortyNineDegreeBlocks_five_top :
    (orderFortyNineDegreeBlocks 5).top = 29632 := by
  native_decide

set_option maxHeartbeats 0 in
theorem orderFortyNineC4Clauses_size :
    orderFortyNineC4Clauses.size = 1271256 := by
  native_decide

theorem orderFortyNineGeneratedCanonicalSatCnf_three_clause_count
    (masks : Array Nat) :
    (orderFortyNineGeneratedCanonicalSatCnf 3 masks).clauses.size =
      1328183 := by
  simp [orderFortyNineGeneratedCanonicalSatCnf,
    orderFortyNineCanonicalFixedClauses_three_size,
    orderFortyNineCanonicalPartitionClauses_three_size,
    orderFortyNineC4Clauses_size,
    orderFortyNineDegreeBlocks_three_clauses_size,
    dimacsFormulaToSatClauses]

theorem orderFortyNineGeneratedCanonicalSatCnf_five_clause_count
    (masks : Array Nat) :
    (orderFortyNineGeneratedCanonicalSatCnf 5 masks).clauses.size =
      1328618 := by
  simp [orderFortyNineGeneratedCanonicalSatCnf,
    orderFortyNineCanonicalFixedClauses_five_size,
    orderFortyNineCanonicalPartitionClauses_five_size,
    orderFortyNineC4Clauses_size,
    orderFortyNineDegreeBlocks_five_clauses_size,
    dimacsFormulaToSatClauses]

theorem orderFortyNineGeneratedCanonicalSatCnf_seven_clause_count
    (masks : Array Nat) :
    (orderFortyNineGeneratedCanonicalSatCnf 7 masks).clauses.size =
      1329041 := by
  simp [orderFortyNineGeneratedCanonicalSatCnf,
    orderFortyNineCanonicalFixedClauses_seven_size,
    orderFortyNineCanonicalPartitionClauses_seven_size,
    orderFortyNineC4Clauses_size,
    orderFortyNineDegreeBlocks_seven_clauses_size,
    dimacsFormulaToSatClauses]

end Erdos85
