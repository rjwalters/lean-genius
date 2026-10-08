import Orbit66
import Certificate_66
namespace Rejection66
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit66.cross g)) := by
  apply Orbit66.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary66.B
  exact SeparatedCanary66.no_joint_literal
end Rejection66
#print axioms Rejection66.no_joint
