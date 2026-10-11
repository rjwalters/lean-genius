import Orbit5
import Certificate_05
namespace Rejection5
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit5.cross g)) := by
  apply Orbit5.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary5.B
  exact SeparatedCanary5.no_joint_literal
end Rejection5
#print axioms Rejection5.no_joint
