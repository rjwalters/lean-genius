import Orbit54
import Certificate_54
namespace Rejection54
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit54.cross g)) := by
  apply Orbit54.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary54.B
  exact SeparatedCanary54.no_joint_literal
end Rejection54
#print axioms Rejection54.no_joint
