import Orbit19
import Certificate_19
namespace Rejection19
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit19.cross g)) := by
  apply Orbit19.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary19.B
  exact SeparatedCanary19.no_joint_literal
end Rejection19
#print axioms Rejection19.no_joint
