import Orbit13
import Certificate_13
namespace Rejection13
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit13.cross g)) := by
  apply Orbit13.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary13.B
  exact SeparatedCanary13.no_joint_literal
end Rejection13
#print axioms Rejection13.no_joint
