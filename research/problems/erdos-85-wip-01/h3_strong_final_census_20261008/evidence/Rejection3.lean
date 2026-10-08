import Orbit3
import Certificate_03
namespace Rejection3
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit3.cross g)) := by
  apply Orbit3.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary3.B
  exact SeparatedCanary3.no_joint_literal
end Rejection3
#print axioms Rejection3.no_joint
