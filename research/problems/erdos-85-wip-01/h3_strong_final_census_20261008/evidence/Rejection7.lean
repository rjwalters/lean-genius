import Orbit7
import Certificate_07
namespace Rejection7
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit7.cross g)) := by
  apply Orbit7.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary7.B
  exact SeparatedCanary7.no_joint_literal
end Rejection7
#print axioms Rejection7.no_joint
