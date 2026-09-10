import Orbit30
import Certificate_30
namespace Rejection30
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit30.cross g)) := by
  apply Orbit30.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary30.B
  exact SeparatedCanary30.no_joint_literal
end Rejection30
#print axioms Rejection30.no_joint
