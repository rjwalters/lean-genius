import Orbit62
import Certificate_62
namespace Rejection62
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit62.cross g)) := by
  apply Orbit62.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary62.B
  exact SeparatedCanary62.no_joint_literal
end Rejection62
#print axioms Rejection62.no_joint
