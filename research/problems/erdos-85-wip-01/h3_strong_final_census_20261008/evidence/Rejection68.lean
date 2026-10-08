import Orbit68
import Certificate_68
namespace Rejection68
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit68.cross g)) := by
  apply Orbit68.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary68.B
  exact SeparatedCanary68.no_joint_literal
end Rejection68
#print axioms Rejection68.no_joint
