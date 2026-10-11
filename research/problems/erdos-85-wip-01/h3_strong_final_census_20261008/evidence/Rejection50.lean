import Orbit50
import Certificate_50
namespace Rejection50
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit50.cross g)) := by
  apply Orbit50.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary50.B
  exact SeparatedCanary50.no_joint_literal
end Rejection50
#print axioms Rejection50.no_joint
