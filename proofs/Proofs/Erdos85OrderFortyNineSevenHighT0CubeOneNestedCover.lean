import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCover

/-! # A second checked split for hard h7/t0 cube-one leaves -/

namespace Erdos85

open Std Sat

/-- The next untouched `N(0)` partition clause, for low vertex `23`.
The variables are zero-based `Std.Sat` identifiers. -/
def sevenHighT0CubeOneNestedLeftVariables : Array Nat :=
  #[1254, 1288, 1322, 1356, 1390, 1424, 1458, 1492]

/-- The corresponding `N(1)` partition clause for low vertex `23`. -/
def sevenHighT0CubeOneNestedRightVariables : Array Nat :=
  #[1254, 1519, 1546, 1573, 1600, 1627, 1654, 1681]

/-- A first-level positive leaf, used as the base of its second checked grid. -/
def sevenHighT0CubeOneNestedBaseCnf
    (parentLeft parentRight : Nat) : CNF Nat :=
  sevenHighT0CubeOnePositiveCnf parentLeft parentRight

def sevenHighT0CubeOneNestedLeftCoverCnf
    (parentLeft parentRight : Nat) : CNF Nat :=
  cnfWithUnits (sevenHighT0CubeOneNestedBaseCnf parentLeft parentRight)
    (negativeUnits sevenHighT0CubeOneNestedLeftVariables)

def sevenHighT0CubeOneNestedRightCoverCnf
    (parentLeft parentRight : Nat) : CNF Nat :=
  cnfWithUnits (sevenHighT0CubeOneNestedBaseCnf parentLeft parentRight)
    (negativeUnits sevenHighT0CubeOneNestedRightVariables)

def sevenHighT0CubeOneNestedPositiveCnf
    (parentLeft parentRight childLeft childRight : Nat) : CNF Nat :=
  cnfWithUnits (sevenHighT0CubeOneNestedBaseCnf parentLeft parentRight)
    (positiveTwoCube childLeft childRight)

/-- A complete second-level checked grid for one hard first-level leaf. -/
structure SevenHighT0CubeOneNestedCheckedGrid
    (parentLeft parentRight : Nat) : Prop where
  leftCover :
    (sevenHighT0CubeOneNestedLeftCoverCnf parentLeft parentRight).Unsat
  rightCover :
    (sevenHighT0CubeOneNestedRightCoverCnf parentLeft parentRight).Unsat
  cubes : ∀ left : Fin sevenHighT0CubeOneNestedLeftVariables.size,
    ∀ right : Fin sevenHighT0CubeOneNestedRightVariables.size,
      (sevenHighT0CubeOneNestedPositiveCnf parentLeft parentRight
        sevenHighT0CubeOneNestedLeftVariables[left.val]
        sevenHighT0CubeOneNestedRightVariables[right.val]).Unsat

/-- A checked nested grid proves its parent first-level leaf unsatisfiable. -/
theorem sevenHighT0CubeOne_parent_unsat_of_nestedCheckedGrid
    {parentLeft parentRight : Nat}
    (grid : SevenHighT0CubeOneNestedCheckedGrid parentLeft parentRight) :
    (sevenHighT0CubeOnePositiveCnf parentLeft parentRight).Unsat := by
  apply cnf_unsat_of_exhaustive_twoCubes
    (sevenHighT0CubeOneNestedBaseCnf parentLeft parentRight)
    sevenHighT0CubeOneNestedLeftVariables
    sevenHighT0CubeOneNestedRightVariables
    grid.leftCover grid.rightCover
  intro left hleft right hright
  obtain ⟨li, hli, hliEq⟩ := Array.getElem_of_mem hleft
  obtain ⟨ri, hri, hriEq⟩ := Array.getElem_of_mem hright
  simpa [sevenHighT0CubeOneNestedPositiveCnf,
    sevenHighT0CubeOneNestedBaseCnf, hliEq, hriEq] using
    grid.cubes ⟨li, hli⟩ ⟨ri, hri⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CubeOne_nestedSelectorSizes :
    (sevenHighT0CubeOneNestedLeftVariables.size,
      sevenHighT0CubeOneNestedRightVariables.size) = (8, 8) := by
  native_decide

end Erdos85

#print axioms Erdos85.sevenHighT0CubeOne_parent_unsat_of_nestedCheckedGrid
