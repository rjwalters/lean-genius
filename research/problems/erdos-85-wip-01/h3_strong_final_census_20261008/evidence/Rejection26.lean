import Orbit26
import Certificate_26
namespace Rejection26
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit26.cross g)) := by
  apply Orbit26.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary26.B
  exact SeparatedCanary26.no_joint_literal
end Rejection26
#print axioms Rejection26.no_joint
