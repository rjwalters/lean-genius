import Orbit39
import Certificate_39
namespace Rejection39
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit39.cross g)) := by
  apply Orbit39.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary39.B
  exact SeparatedCanary39.no_joint_literal
end Rejection39
#print axioms Rejection39.no_joint
