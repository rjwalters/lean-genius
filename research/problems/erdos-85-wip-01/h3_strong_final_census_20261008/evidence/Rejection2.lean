import Orbit2
import Certificate_02
namespace Rejection2
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit2.cross g)) := by
  apply Orbit2.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary2.B
  exact SeparatedCanary2.no_joint_literal
end Rejection2
#print axioms Rejection2.no_joint
