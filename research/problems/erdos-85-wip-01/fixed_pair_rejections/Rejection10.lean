import Orbit10
import Certificate_10
namespace Rejection10
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit10.cross g)) := by
  apply Orbit10.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary10.B
  exact SeparatedCanary10.no_joint_literal
end Rejection10
#print axioms Rejection10.no_joint
