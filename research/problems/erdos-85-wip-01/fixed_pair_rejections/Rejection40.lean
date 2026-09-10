import Orbit40
import Certificate_40
namespace Rejection40
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit40.cross g)) := by
  apply Orbit40.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary40.B
  exact SeparatedCanary40.no_joint_literal
end Rejection40
#print axioms Rejection40.no_joint
