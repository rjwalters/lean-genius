import Orbit16
import Certificate_16
namespace Rejection16
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit16.cross g)) := by
  apply Orbit16.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary16.B
  exact SeparatedCanary16.no_joint_literal
end Rejection16
#print axioms Rejection16.no_joint
