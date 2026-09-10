import Orbit43
import Certificate_43
namespace Rejection43
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit43.cross g)) := by
  apply Orbit43.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary43.B
  exact SeparatedCanary43.no_joint_literal
end Rejection43
#print axioms Rejection43.no_joint
