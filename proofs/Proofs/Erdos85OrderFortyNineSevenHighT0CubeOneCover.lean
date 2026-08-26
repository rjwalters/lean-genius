import Proofs.Erdos85CnfCubeCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCnfSound
import Proofs.Erdos85OrderFortyNineT0TwoCubeBridge

/-!
# Checked sub-cube cover for the hard seven-high cube one

Residual symmetry reduces the seven original `h = 7, t = 0` selector cubes
to cube zero, which is structurally impossible, and cube one.  This module
splits that remaining 1.33-million-clause CNF along two genuinely unpinned
adjacency-partition clauses for low vertex `22`.  Each clause has eight
candidates, so a complete checked package consists of two negative cover
checks and an `8 × 8` grid of positive two-unit checks.
-/

namespace Erdos85

open Std Sat

/-- The partition clause saying that low vertex `22` meets `N(0)=7..14`.
These are the generator's zero-based identifiers for edges
`22--7, ..., 22--14`. -/
def sevenHighT0CubeOneLeftVariables : Array Nat :=
  #[1253, 1287, 1321, 1355, 1389, 1423, 1457, 1491]

/-- The partition clause saying that low vertex `22` meets
`N(1)={7,15,..,21}`. -/
def sevenHighT0CubeOneRightVariables : Array Nat :=
  #[1253, 1518, 1545, 1572, 1599, 1626, 1653, 1680]

def sevenHighT0CubeOneLeftCoverCnf : CNF Nat :=
  cnfWithUnits (orderFortyNineGeneratedH7T0CubeSatCnf 1)
    (negativeUnits sevenHighT0CubeOneLeftVariables)

def sevenHighT0CubeOneRightCoverCnf : CNF Nat :=
  cnfWithUnits (orderFortyNineGeneratedH7T0CubeSatCnf 1)
    (negativeUnits sevenHighT0CubeOneRightVariables)

def sevenHighT0CubeOnePositiveCnf (left right : Nat) : CNF Nat :=
  cnfWithUnits (orderFortyNineGeneratedH7T0CubeSatCnf 1)
    (positiveTwoCube left right)

/-- Generator-facing package whose finite indices make a missing grid leaf
impossible at assembly time. -/
structure SevenHighT0CubeOneCheckedGrid : Prop where
  leftCover : sevenHighT0CubeOneLeftCoverCnf.Unsat
  rightCover : sevenHighT0CubeOneRightCoverCnf.Unsat
  cubes : ∀ left : Fin sevenHighT0CubeOneLeftVariables.size,
    ∀ right : Fin sevenHighT0CubeOneRightVariables.size,
      (sevenHighT0CubeOnePositiveCnf
        sevenHighT0CubeOneLeftVariables[left.val]
        sevenHighT0CubeOneRightVariables[right.val]).Unsat

theorem sevenHighT0CubeOne_unsat_of_checkedGrid
    (grid : SevenHighT0CubeOneCheckedGrid) :
    (orderFortyNineGeneratedH7T0CubeSatCnf 1).Unsat := by
  apply cnf_unsat_of_exhaustive_twoCubes
    (orderFortyNineGeneratedH7T0CubeSatCnf 1)
    sevenHighT0CubeOneLeftVariables sevenHighT0CubeOneRightVariables
    grid.leftCover grid.rightCover
  intro left hleft right hright
  obtain ⟨li, hli, hliEq⟩ := Array.getElem_of_mem hleft
  obtain ⟨ri, hri, hriEq⟩ := Array.getElem_of_mem hright
  simpa [sevenHighT0CubeOnePositiveCnf, hliEq, hriEq] using
    grid.cubes ⟨li, hli⟩ ⟨ri, hri⟩

/-- An unsatisfiable cube-one CNF closes the canonical representative; cube
zero is discharged by the existing structural common-neighbor contradiction.
-/
theorem sevenHighT0_canonicalExcluded_of_cubeOne_unsat_provedSound
    (hunsat : (orderFortyNineGeneratedH7T0CubeSatCnf 1).Unsat) :
    SevenHighCanonicalRepresentativeExcluded 0 0 := by
  apply sevenHighT0CoreExcluded_to_canonical
  intro edges hedges
  obtain ⟨cube, normalizedEdges, hnormalized⟩ :=
    sevenHighT0_exists_normalized_relationCore_zero_or_one edges hedges
  fin_cases cube
  · exact sevenHighT0_relationCore_zero_false
      (orderFortyNineBitAdj normalizedEdges)
      (orderFortyNineBitAdj_comm normalizedEdges) hnormalized
  · obtain ⟨assignment, hsat⟩ :=
      sevenHighT0CubeOneCnfSound_proved normalizedEdges hnormalized
    have hfalse := hunsat assignment
    rw [hsat] at hfalse
    contradiction

/-- The direct checked-cover endpoint for the hard `h = 7, t = 0` leaf. -/
theorem sevenHighT0_canonicalExcluded_of_cubeOne_checkedGrid
    (grid : SevenHighT0CubeOneCheckedGrid) :
    SevenHighCanonicalRepresentativeExcluded 0 0 :=
  sevenHighT0_canonicalExcluded_of_cubeOne_unsat_provedSound
    (sevenHighT0CubeOne_unsat_of_checkedGrid grid)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CubeOne_selector_sizes :
    (sevenHighT0CubeOneLeftVariables.size,
      sevenHighT0CubeOneRightVariables.size) = (8, 8) := by
  native_decide

end Erdos85

#print axioms Erdos85.sevenHighT0CubeOne_unsat_of_checkedGrid
#print axioms Erdos85.sevenHighT0_canonicalExcluded_of_cubeOne_checkedGrid
