import CoverageCoordinates
import OrderedLeaves
namespace ColumnCoverageFixedPair
open Erdos85 ColumnCoverageLiterals
theorem table_eq : table = FixedPairOrderedLeaves.cross := rfl

theorem table_no_joint (entry : Fin 140) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R (table entry)) := by
  rw [U_eq, R_eq, table_eq]
  exact FixedPairOrderedLeaves.no_joint entry

end ColumnCoverageFixedPair
#print axioms ColumnCoverageFixedPair.table_eq
#print axioms ColumnCoverageFixedPair.table_no_joint
