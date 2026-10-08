import LiteralData
open Erdos85
namespace ColumnCoverageLiterals
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
theorem U_eq : U = threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)) := by
  funext i j
  revert i j
  decide
theorem R_eq : R = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14) := by
  funext i j
  revert i j
  decide
end ColumnCoverageLiterals
#print axioms ColumnCoverageLiterals.U_eq
#print axioms ColumnCoverageLiterals.R_eq
