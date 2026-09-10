import Orbit17
import Certificate_17
namespace Rejection17
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit17.cross g)) := by
  apply Orbit17.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary17.B
  exact SeparatedCanary17.no_joint_literal
end Rejection17
#print axioms Rejection17.no_joint
