import Orbit47
import Certificate_47
namespace Rejection47
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit47.cross g)) := by
  apply Orbit47.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary47.B
  exact SeparatedCanary47.no_joint_literal
end Rejection47
#print axioms Rejection47.no_joint
