import Proofs.Erdos85OrderFortyNineSmallHighNestedCubeSelectors

/-!
# Third-level selectors for the four hardest three-high parents

The first four parents in the stopped Tier-A queue are the `b1` parent and
three `c1` parents.  Those cells share the no-coincidence mask vector.  After
the first two checked grids, the next two low vertices give another pair of
independent partition clauses.  The generic checked-grid theorem can therefore
be instantiated once more on every positive second-level child CNF.
-/

namespace Erdos85

/-- Third-level left partition for the common `b1`/`c1` mask vector. -/
def orderFortyNineThreeHighHardThirdCubeLeftVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (23 : Fin 46) (0 : Fin 3)

/-- Third-level right partition, disjoint from the left partition. -/
def orderFortyNineThreeHighHardThirdCubeRightVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (24 : Fin 46) (0 : Fin 3)

/-- Generator-facing pin: these are the one-based DIMACS identifiers printed
by the exact emitter after adding one to Lean's zero-based SAT identifiers. -/
theorem orderFortyNineThreeHighHardThirdCube_selector_values :
    (orderFortyNineThreeHighHardThirdCubeLeftVariables.map (· + 1),
      orderFortyNineThreeHighHardThirdCubeRightVariables.map (· + 1)) =
      (#[164, 208, 293, 334, 374, 413, 451, 488],
       #[165, 209, 294, 335, 375, 414, 452, 489]) := by
  native_decide

/-- Both third-level clauses have eight candidates. -/
theorem orderFortyNineThreeHighHardThirdCube_selector_sizes :
    (orderFortyNineThreeHighHardThirdCubeLeftVariables.size,
      orderFortyNineThreeHighHardThirdCubeRightVariables.size) = (8, 8) := by
  native_decide

/-- The third-level selector clauses are genuinely independent. -/
theorem orderFortyNineThreeHighHardThirdCube_selectors_disjoint :
    orderFortyNineThreeHighHardThirdCubeLeftVariables.all (fun id =>
      !orderFortyNineThreeHighHardThirdCubeRightVariables.contains id) = true := by
  native_decide

end Erdos85
