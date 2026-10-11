import Orbit48
import Certificate_48
namespace Rejection48
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit48.cross g)) := by
  apply Orbit48.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary48.B
  exact SeparatedCanary48.no_joint_literal
end Rejection48
#print axioms Rejection48.no_joint
