import Orbit29
import Certificate_29
namespace Rejection29
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit29.cross g)) := by
  apply Orbit29.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary29.B
  exact SeparatedCanary29.no_joint_literal
end Rejection29
#print axioms Rejection29.no_joint
