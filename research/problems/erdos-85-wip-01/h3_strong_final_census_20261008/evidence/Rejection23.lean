import Orbit23
import Certificate_23
namespace Rejection23
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit23.cross g)) := by
  apply Orbit23.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary23.B
  exact SeparatedCanary23.no_joint_literal
end Rejection23
#print axioms Rejection23.no_joint
