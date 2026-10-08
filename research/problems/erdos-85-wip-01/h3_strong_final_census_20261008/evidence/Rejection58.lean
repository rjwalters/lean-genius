import Orbit58
import Certificate_58
namespace Rejection58
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit58.cross g)) := by
  apply Orbit58.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary58.B
  exact SeparatedCanary58.no_joint_literal
end Rejection58
#print axioms Rejection58.no_joint
