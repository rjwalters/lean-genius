import Orbit1
import Certificate_01
namespace Rejection1
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit1.cross g)) := by
  apply Orbit1.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary1.B
  exact SeparatedCanary1.no_joint_literal
end Rejection1
#print axioms Rejection1.no_joint
