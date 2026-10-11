import Orbit33
import Special33
namespace Rejection33
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit33.cross g)) := by
  apply Orbit33.no_joint_cross
  change ¬ ThreeHighJointWitness ExactCoverCanary.B
  exact ExactCoverCanary.no_joint_literal
end Rejection33
#print axioms Rejection33.no_joint
