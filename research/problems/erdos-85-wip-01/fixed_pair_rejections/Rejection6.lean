import Orbit6
import Certificate_06
namespace Rejection6
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit6.cross g)) := by
  apply Orbit6.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary6.B
  exact SeparatedCanary6.no_joint_literal
end Rejection6
#print axioms Rejection6.no_joint
