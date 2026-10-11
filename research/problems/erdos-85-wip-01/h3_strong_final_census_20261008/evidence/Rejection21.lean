import Orbit21
import Certificate_21
namespace Rejection21
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit21.cross g)) := by
  apply Orbit21.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary21.B
  exact SeparatedCanary21.no_joint_literal
end Rejection21
#print axioms Rejection21.no_joint
