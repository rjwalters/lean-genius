import Orbit18
import Certificate_18
namespace Rejection18
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit18.cross g)) := by
  apply Orbit18.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary18.B
  exact SeparatedCanary18.no_joint_literal
end Rejection18
#print axioms Rejection18.no_joint
