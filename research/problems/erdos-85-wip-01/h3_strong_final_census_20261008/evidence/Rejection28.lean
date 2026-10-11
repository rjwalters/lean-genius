import Orbit28
import Certificate_28
namespace Rejection28
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit28.cross g)) := by
  apply Orbit28.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary28.B
  exact SeparatedCanary28.no_joint_literal
end Rejection28
#print axioms Rejection28.no_joint
