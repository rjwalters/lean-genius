import Orbit61
import Certificate_61
namespace Rejection61
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit61.cross g)) := by
  apply Orbit61.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary61.B
  exact SeparatedCanary61.no_joint_literal
end Rejection61
#print axioms Rejection61.no_joint
