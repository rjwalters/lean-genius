import Orbit12
import Certificate_12
namespace Rejection12
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit12.cross g)) := by
  apply Orbit12.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary12.B
  exact SeparatedCanary12.no_joint_literal
end Rejection12
#print axioms Rejection12.no_joint
