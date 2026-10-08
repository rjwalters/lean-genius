import Orbit42
import Certificate_42
namespace Rejection42
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit42.cross g)) := by
  apply Orbit42.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary42.B
  exact SeparatedCanary42.no_joint_literal
end Rejection42
#print axioms Rejection42.no_joint
