import Orbit56
import Certificate_56
namespace Rejection56
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit56.cross g)) := by
  apply Orbit56.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary56.B
  exact SeparatedCanary56.no_joint_literal
end Rejection56
#print axioms Rejection56.no_joint
