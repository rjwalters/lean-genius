import Orbit34
import Certificate_34
namespace Rejection34
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit34.cross g)) := by
  apply Orbit34.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary34.B
  exact SeparatedCanary34.no_joint_literal
end Rejection34
#print axioms Rejection34.no_joint
