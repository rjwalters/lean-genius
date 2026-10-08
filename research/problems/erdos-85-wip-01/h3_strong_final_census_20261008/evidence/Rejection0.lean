import Orbit0
import Certificate_00
namespace Rejection0
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit0.cross g)) := by
  apply Orbit0.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary0.B
  exact SeparatedCanary0.no_joint_literal
end Rejection0
#print axioms Rejection0.no_joint
