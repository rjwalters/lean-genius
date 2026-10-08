import Orbit44
import Certificate_44
namespace Rejection44
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit44.cross g)) := by
  apply Orbit44.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary44.B
  exact SeparatedCanary44.no_joint_literal
end Rejection44
#print axioms Rejection44.no_joint
