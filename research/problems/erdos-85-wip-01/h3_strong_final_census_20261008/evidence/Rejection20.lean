import Orbit20
import Certificate_20
namespace Rejection20
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit20.cross g)) := by
  apply Orbit20.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary20.B
  exact SeparatedCanary20.no_joint_literal
end Rejection20
#print axioms Rejection20.no_joint
