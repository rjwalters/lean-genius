import Orbit36
import Certificate_36
namespace Rejection36
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit36.cross g)) := by
  apply Orbit36.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary36.B
  exact SeparatedCanary36.no_joint_literal
end Rejection36
#print axioms Rejection36.no_joint
