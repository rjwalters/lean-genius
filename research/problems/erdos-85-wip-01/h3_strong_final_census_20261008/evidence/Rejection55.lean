import Orbit55
import Certificate_55
namespace Rejection55
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit55.cross g)) := by
  apply Orbit55.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary55.B
  exact SeparatedCanary55.no_joint_literal
end Rejection55
#print axioms Rejection55.no_joint
