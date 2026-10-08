import Orbit35
import Certificate_35
namespace Rejection35
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit35.cross g)) := by
  apply Orbit35.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary35.B
  exact SeparatedCanary35.no_joint_literal
end Rejection35
#print axioms Rejection35.no_joint
