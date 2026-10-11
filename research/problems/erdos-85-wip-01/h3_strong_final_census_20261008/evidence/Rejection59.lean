import Orbit59
import Certificate_59
namespace Rejection59
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit59.cross g)) := by
  apply Orbit59.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary59.B
  exact SeparatedCanary59.no_joint_literal
end Rejection59
#print axioms Rejection59.no_joint
