import Orbit38
import Certificate_38
namespace Rejection38
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit38.cross g)) := by
  apply Orbit38.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary38.B
  exact SeparatedCanary38.no_joint_literal
end Rejection38
#print axioms Rejection38.no_joint
