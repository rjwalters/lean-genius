import Orbit64
import Certificate_64
namespace Rejection64
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit64.cross g)) := by
  apply Orbit64.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary64.B
  exact SeparatedCanary64.no_joint_literal
end Rejection64
#print axioms Rejection64.no_joint
