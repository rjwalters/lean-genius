import Proofs.Erdos85CnfCubeCover
import Proofs.Erdos85OrderFortyNineThreeHighScoutCnf

/-!
# Checked cube-cover interface for the hard three- and five-high cells

The selectors are the positive edge variables in two adjacency-partition
clauses.  External cube-and-conquer jobs may check the two negative cover
formulas and every positive Cartesian cube.  Finite indexing makes an omitted
cube impossible when the resulting certificate module is assembled.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Zero-based SAT identifiers of the edge literals in one variable-high
partition clause.  These are exactly the candidates whose disjunction is
already present in the base CNF. -/
def orderFortyNineSmallHighPartitionCubeVariables
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (y : Fin (49 - h.val)) (w : Fin h.val) : Array Nat :=
  (((orderFortyNineVariablePartitionNeighbors h masks w).filter fun x =>
      x ≠ orderFortyNineVariableLowVertex h y).map fun x =>
        (orderFortyNineEdgeLiteral
          (orderFortyNineVariableLowVertex h y) x).natAbs - 1).toArray

/-- The standard left selector uses the first low vertex and first high
vertex. -/
def orderFortyNineThreeHighCubeLeftVariables (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) masks (0 : Fin 46) (0 : Fin 3)

/-- The standard right selector uses the second low vertex and second high
vertex, hence is a genuinely different partition clause. -/
def orderFortyNineThreeHighCubeRightVariables (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) masks (1 : Fin 46) (1 : Fin 3)

def orderFortyNineFiveHighCubeLeftVariables (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (5 : Fin 50) masks (0 : Fin 44) (0 : Fin 5)

def orderFortyNineFiveHighCubeRightVariables (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (5 : Fin 50) masks (1 : Fin 44) (1 : Fin 5)

def orderFortyNineSmallHighLeftCoverCnf
    (base : CNF Nat) (left : Array Nat) : CNF Nat :=
  cnfWithUnits base (negativeUnits left)

def orderFortyNineSmallHighRightCoverCnf
    (base : CNF Nat) (right : Array Nat) : CNF Nat :=
  cnfWithUnits base (negativeUnits right)

def orderFortyNineSmallHighPositiveCubeCnf
    (base : CNF Nat) (left right : Nat) : CNF Nat :=
  cnfWithUnits base (positiveTwoCube left right)

/-- Generator-facing checked package.  The two cover checks prove that every
base model selects a variable on each side; the finite grid then excludes all
possible selections. -/
structure OrderFortyNineSmallHighCheckedCubeGrid
    (base : CNF Nat) (left right : Array Nat) : Prop where
  leftCover : (orderFortyNineSmallHighLeftCoverCnf base left).Unsat
  rightCover : (orderFortyNineSmallHighRightCoverCnf base right).Unsat
  cubes : ∀ li : Fin left.size, ∀ ri : Fin right.size,
    (orderFortyNineSmallHighPositiveCubeCnf
      base left[li.val] right[ri.val]).Unsat

set_option maxHeartbeats 0 in
/-- A complete checked grid refutes the exact base CNF. -/
theorem orderFortyNineSmallHigh_unsat_of_checkedCubeGrid
    {base : CNF Nat} {left right : Array Nat}
    (grid : OrderFortyNineSmallHighCheckedCubeGrid base left right) :
    base.Unsat := by
  apply cnf_unsat_of_exhaustive_twoCubes base left right
    grid.leftCover grid.rightCover
  intro l hl r hr
  obtain ⟨li, hli, hliEq⟩ := Array.getElem_of_mem hl
  obtain ⟨ri, hri, hriEq⟩ := Array.getElem_of_mem hr
  simpa [orderFortyNineSmallHighPositiveCubeCnf, hliEq, hriEq] using
    grid.cubes ⟨li, hli⟩ ⟨ri, hri⟩

/-- The four hard three-high scout cells paired with their canonical masks. -/
def orderFortyNineThreeHighCubeCells :
    List (CNF Nat × Array Nat) :=
  [ (orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf,
      orderFortyNineThreeHighDistOneNoCoincidenceMasks),
    (orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf,
      orderFortyNineThreeHighDistOneNoCoincidenceMasks),
    (orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf,
      orderFortyNineThreeHighDistOneC2Masks),
    (orderFortyNineGeneratedThreeHighDistTwoScoutCnf,
      orderFortyNineThreeHighDistTwoMasks) ]

/-- The three hard five-high cells paired with their canonical masks. -/
def orderFortyNineFiveHighCubeCells :
    List (CNF Nat × Array Nat) :=
  [ (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT0Masks, orderFortyNineFiveHighT0Masks),
    (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT1Masks, orderFortyNineFiveHighT1Masks),
    (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT2Masks, orderFortyNineFiveHighT2Masks) ]

/-- All selected partition clauses have seven or eight candidates, so every
cell expands to at most 64 positive two-unit cubes plus two cover checks. -/
theorem orderFortyNineThreeHighCubeCell_selector_bounds :
    orderFortyNineThreeHighCubeCells.all (fun cell =>
      let left := orderFortyNineThreeHighCubeLeftVariables cell.2
      let right := orderFortyNineThreeHighCubeRightVariables cell.2
      0 < left.size && left.size ≤ 8 &&
        0 < right.size && right.size ≤ 8) = true := by
  native_decide

theorem orderFortyNineFiveHighCubeCell_selector_bounds :
    orderFortyNineFiveHighCubeCells.all (fun cell =>
      let left := orderFortyNineFiveHighCubeLeftVariables cell.2
      let right := orderFortyNineFiveHighCubeRightVariables cell.2
      0 < left.size && left.size ≤ 8 &&
      0 < right.size && right.size ≤ 8) = true := by
  native_decide

/-- In cell order `b1,c1,c2,dist2`, every three-high grid is exactly 7 by 8. -/
theorem orderFortyNineThreeHighCubeCell_selector_sizes :
    orderFortyNineThreeHighCubeCells.map (fun cell =>
      ((orderFortyNineThreeHighCubeLeftVariables cell.2).size,
        (orderFortyNineThreeHighCubeRightVariables cell.2).size)) =
      [(7, 8), (7, 8), (7, 8), (7, 8)] := by
  native_decide

/-- In cell order `t0,t1,t2`, every five-high grid is exactly 7 by 8. -/
theorem orderFortyNineFiveHighCubeCell_selector_sizes :
    orderFortyNineFiveHighCubeCells.map (fun cell =>
      ((orderFortyNineFiveHighCubeLeftVariables cell.2).size,
        (orderFortyNineFiveHighCubeRightVariables cell.2).size)) =
      [(7, 8), (7, 8), (7, 8)] := by
  native_decide

/-- The seven h3/h5 cells therefore require 392 positive cube refutations
and fourteen inexpensive negative cover refutations. -/
theorem orderFortyNineSmallHigh_positiveCube_job_count :
    4 * (7 * 8) + 3 * (7 * 8) = 392 := by
  norm_num

end Erdos85
