import U20Data
open Erdos85
namespace U20CoverageLiterals
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
theorem U_eq : U = threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)) := by
  funext i j
  revert i j
  decide
theorem R_eq : R = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14) := by
  funext i j
  revert i j
  decide
end U20CoverageLiterals
#print axioms U20CoverageLiterals.U_eq
#print axioms U20CoverageLiterals.R_eq
