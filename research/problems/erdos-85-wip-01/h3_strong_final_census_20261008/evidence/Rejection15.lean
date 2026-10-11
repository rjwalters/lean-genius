import Orbit15
import Special15
namespace Rejection15
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit15.cross g)) := by
  apply Orbit15.no_joint_cross
  change ¬ ThreeHighJointWitness JointCanary.B
  exact JointCanary.no_joint_literal
end Rejection15
#print axioms Rejection15.no_joint
