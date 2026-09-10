import Orbit25
import Certificate_25
namespace Rejection25
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit25.cross g)) := by
  apply Orbit25.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary25.B
  exact SeparatedCanary25.no_joint_literal
end Rejection25
#print axioms Rejection25.no_joint
