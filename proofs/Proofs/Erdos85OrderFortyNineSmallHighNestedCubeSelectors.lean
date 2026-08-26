import Proofs.Erdos85OrderFortyNineSmallHighCubeCover

/-!
# Independent second-level selectors for hard small-high cubes

The first checked split uses partition clauses `(low 0, high 0)` and
`(low 1, high 1)`.  Hard leaves may be split again with the independent
clauses below.  The existing `OrderFortyNineSmallHighCheckedCubeGrid` is
generic in its base CNF, so it can be instantiated directly on a first-level
positive two-unit cube; no additional trusted composition theorem is needed.
-/

namespace Erdos85

def orderFortyNineThreeHighNestedCubeLeftVariables
    (masks : Array Nat) : Array Nat :=
  if masks = orderFortyNineThreeHighDistTwoMasks then
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (2 : Fin 46) (1 : Fin 3)
  else if masks = orderFortyNineThreeHighDistOneC2Masks then
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (8 : Fin 46) (0 : Fin 3)
  else
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (21 : Fin 46) (0 : Fin 3)

def orderFortyNineThreeHighNestedCubeRightVariables
    (masks : Array Nat) : Array Nat :=
  if masks = orderFortyNineThreeHighDistTwoMasks then
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (2 : Fin 46) (2 : Fin 3)
  else if masks = orderFortyNineThreeHighDistOneC2Masks then
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (21 : Fin 46) (0 : Fin 3)
  else
    orderFortyNineSmallHighPartitionCubeVariables
      (3 : Fin 50) masks (22 : Fin 46) (0 : Fin 3)

def orderFortyNineFiveHighNestedCubeLeftVariables
    (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (5 : Fin 50) masks (2 : Fin 44) (2 : Fin 5)

def orderFortyNineFiveHighNestedCubeRightVariables
    (masks : Array Nat) : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (5 : Fin 50) masks (3 : Fin 44) (3 : Fin 5)

/-- All seven second-level selector pairs are nonempty and have at most eight
candidates, matching the first-level operational envelope. -/
theorem orderFortyNineSmallHighNestedCube_selector_bounds :
    (orderFortyNineThreeHighCubeCells.all (fun cell =>
      let left := orderFortyNineThreeHighNestedCubeLeftVariables cell.2
      let right := orderFortyNineThreeHighNestedCubeRightVariables cell.2
      0 < left.size && left.size ≤ 8 &&
        0 < right.size && right.size ≤ 8)) &&
    (orderFortyNineFiveHighCubeCells.all (fun cell =>
      let left := orderFortyNineFiveHighNestedCubeLeftVariables cell.2
      let right := orderFortyNineFiveHighNestedCubeRightVariables cell.2
      0 < left.size && left.size ≤ 8 &&
        0 < right.size && right.size ≤ 8)) = true := by
  native_decide

end Erdos85
