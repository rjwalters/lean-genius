import Orbit37
import Certificate_37
namespace Rejection37
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit37.cross g)) := by
  apply Orbit37.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary37.B
  exact SeparatedCanary37.no_joint_literal
end Rejection37
#print axioms Rejection37.no_joint
