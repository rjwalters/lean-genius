import Orbit52
import Certificate_52
namespace Rejection52
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit52.cross g)) := by
  apply Orbit52.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary52.B
  exact SeparatedCanary52.no_joint_literal
end Rejection52
#print axioms Rejection52.no_joint
