import Orbit31
import Certificate_31
namespace Rejection31
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit31.cross g)) := by
  apply Orbit31.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary31.B
  exact SeparatedCanary31.no_joint_literal
end Rejection31
#print axioms Rejection31.no_joint
