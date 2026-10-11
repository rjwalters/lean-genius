import Orbit41
import Certificate_41
namespace Rejection41
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit41.cross g)) := by
  apply Orbit41.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary41.B
  exact SeparatedCanary41.no_joint_literal
end Rejection41
#print axioms Rejection41.no_joint
