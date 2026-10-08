import Orbit46
import Certificate_46
namespace Rejection46
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit46.cross g)) := by
  apply Orbit46.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary46.B
  exact SeparatedCanary46.no_joint_literal
end Rejection46
#print axioms Rejection46.no_joint
