import Orbit32
import Certificate_32
namespace Rejection32
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit32.cross g)) := by
  apply Orbit32.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary32.B
  exact SeparatedCanary32.no_joint_literal
end Rejection32
#print axioms Rejection32.no_joint
