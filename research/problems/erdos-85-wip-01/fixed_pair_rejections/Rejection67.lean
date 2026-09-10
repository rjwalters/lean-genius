import Orbit67
import Certificate_67
namespace Rejection67
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit67.cross g)) := by
  apply Orbit67.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary67.B
  exact SeparatedCanary67.no_joint_literal
end Rejection67
#print axioms Rejection67.no_joint
