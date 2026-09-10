import Orbit22
import Certificate_22
namespace Rejection22
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit22.cross g)) := by
  apply Orbit22.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary22.B
  exact SeparatedCanary22.no_joint_literal
end Rejection22
#print axioms Rejection22.no_joint
