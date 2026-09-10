import Orbit57
import Certificate_57
namespace Rejection57
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit57.cross g)) := by
  apply Orbit57.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary57.B
  exact SeparatedCanary57.no_joint_literal
end Rejection57
#print axioms Rejection57.no_joint
