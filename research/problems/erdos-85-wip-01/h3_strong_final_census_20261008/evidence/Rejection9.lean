import Orbit9
import Certificate_09
namespace Rejection9
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit9.cross g)) := by
  apply Orbit9.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary9.B
  exact SeparatedCanary9.no_joint_literal
end Rejection9
#print axioms Rejection9.no_joint
