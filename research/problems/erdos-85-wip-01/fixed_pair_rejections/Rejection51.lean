import Orbit51
import Certificate_51
namespace Rejection51
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit51.cross g)) := by
  apply Orbit51.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary51.B
  exact SeparatedCanary51.no_joint_literal
end Rejection51
#print axioms Rejection51.no_joint
