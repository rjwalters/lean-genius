import Orbit27
import Certificate_27
namespace Rejection27
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit27.cross g)) := by
  apply Orbit27.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary27.B
  exact SeparatedCanary27.no_joint_literal
end Rejection27
#print axioms Rejection27.no_joint
