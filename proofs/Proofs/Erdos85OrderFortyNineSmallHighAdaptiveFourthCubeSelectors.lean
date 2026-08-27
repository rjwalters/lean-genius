import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdCubeSelectors

/-!
# Adaptive fourth-level selectors for the hard `b1` residue

After the structural third split leaves sixteen cells, an exhaustive rank of
the remaining exact positive partition clauses selects low vertices `21` and
`22` in the high-`1` partition.  These axes are not satisfied by any fixed or
live third-level selector literal.  Their Lean/DIMACS identities are pinned
here; the C4 witness table is kept in a separate consumer module.
-/

namespace Erdos85

/-- Left fourth partition: low vertex `21`, high vertex `1`. -/
def orderFortyNineThreeHighB1AdaptiveFourthCubeLeftVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (18 : Fin 46) (1 : Fin 3)

/-- Right fourth partition: low vertex `22`, high vertex `1`. -/
def orderFortyNineThreeHighB1AdaptiveFourthCubeRightVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (19 : Fin 46) (1 : Fin 3)

/-- One-based DIMACS identifiers consumed by a fourth-level job generator. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthCube_selector_values :
    (orderFortyNineThreeHighB1AdaptiveFourthCubeLeftVariables.map (· + 1),
      orderFortyNineThreeHighB1AdaptiveFourthCubeRightVariables.map (· + 1)) =
      (#[159, 246, 519, 554, 588, 621, 653, 684],
       #[160, 247, 520, 555, 589, 622, 654, 685]) := by
  native_decide

theorem orderFortyNineThreeHighB1AdaptiveFourthCube_selector_sizes :
    (orderFortyNineThreeHighB1AdaptiveFourthCubeLeftVariables.size,
      orderFortyNineThreeHighB1AdaptiveFourthCubeRightVariables.size) =
      (8, 8) := by
  native_decide

theorem orderFortyNineThreeHighB1AdaptiveFourthCube_selectors_disjoint :
    orderFortyNineThreeHighB1AdaptiveFourthCubeLeftVariables.all (fun id =>
      !orderFortyNineThreeHighB1AdaptiveFourthCubeRightVariables.contains id) =
      true := by
  native_decide

end Erdos85
