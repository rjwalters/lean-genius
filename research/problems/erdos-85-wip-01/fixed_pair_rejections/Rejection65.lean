import Orbit65
import Certificate_65
namespace Rejection65
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit65.cross g)) := by
  apply Orbit65.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary65.B
  exact SeparatedCanary65.no_joint_literal
end Rejection65
#print axioms Rejection65.no_joint
