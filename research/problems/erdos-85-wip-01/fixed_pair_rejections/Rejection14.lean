import Orbit14
import Certificate_14
namespace Rejection14
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit14.cross g)) := by
  apply Orbit14.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary14.B
  exact SeparatedCanary14.no_joint_literal
end Rejection14
#print axioms Rejection14.no_joint
