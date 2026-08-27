import Proofs.Erdos85OrderFortyNineSmallHighNestedCubeSelectors

/-!
# Structurally ranked third-level selectors for the hard `b1` leaf

The original third-level split uses low vertices `26` and `27` in the
high-`0` partition.  On the canonical `b1.cube-0-0.nested.cube-0-0`
parent, its fixed degree and matching data immediately refute only one of
the resulting 64 positive cubes.

An exhaustive check of the exact positive partition clauses instead selects
low vertices `18` and `20` in the high-`1` partition.  The fixed `b1`
matching and universal C4 clauses immediately refute 48 of those 64 cubes;
only 16 require nontrivial certificates.  This module pins the alternative
selectors at the Lean/DIMACS boundary.  The structural 48-cube consumer is
kept separate from these generator-facing identities.
-/

namespace Erdos85

/-- Left adaptive partition: low vertex `18`, high vertex `1`. -/
def orderFortyNineThreeHighB1AdaptiveThirdCubeLeftVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (15 : Fin 46) (1 : Fin 3)

/-- Right adaptive partition: low vertex `20`, high vertex `1`. -/
def orderFortyNineThreeHighB1AdaptiveThirdCubeRightVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (17 : Fin 46) (1 : Fin 3)

/-- One-based DIMACS identifiers consumed by the adaptive job generator. -/
theorem orderFortyNineThreeHighB1AdaptiveThirdCube_selector_values :
    (orderFortyNineThreeHighB1AdaptiveThirdCubeLeftVariables.map (· + 1),
      orderFortyNineThreeHighB1AdaptiveThirdCubeRightVariables.map (· + 1)) =
      (#[156, 243, 516, 551, 585, 618, 650, 681],
       #[158, 245, 518, 553, 587, 620, 652, 683]) := by
  native_decide

theorem orderFortyNineThreeHighB1AdaptiveThirdCube_selector_sizes :
    (orderFortyNineThreeHighB1AdaptiveThirdCubeLeftVariables.size,
      orderFortyNineThreeHighB1AdaptiveThirdCubeRightVariables.size) =
      (8, 8) := by
  native_decide

theorem orderFortyNineThreeHighB1AdaptiveThirdCube_selectors_disjoint :
    orderFortyNineThreeHighB1AdaptiveThirdCubeLeftVariables.all (fun id =>
      !orderFortyNineThreeHighB1AdaptiveThirdCubeRightVariables.contains id) =
      true := by
  native_decide

end Erdos85
