import Orbit11
import Certificate_11
namespace Rejection11
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit11.cross g)) := by
  apply Orbit11.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary11.B
  exact SeparatedCanary11.no_joint_literal
end Rejection11
#print axioms Rejection11.no_joint
