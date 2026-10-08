import Orbit4
import Certificate_04
namespace Rejection4
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit4.cross g)) := by
  apply Orbit4.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary4.B
  exact SeparatedCanary4.no_joint_literal
end Rejection4
#print axioms Rejection4.no_joint
