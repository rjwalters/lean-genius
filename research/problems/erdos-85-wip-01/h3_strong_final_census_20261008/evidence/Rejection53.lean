import Orbit53
import Certificate_53
namespace Rejection53
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit53.cross g)) := by
  apply Orbit53.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary53.B
  exact SeparatedCanary53.no_joint_literal
end Rejection53
#print axioms Rejection53.no_joint
