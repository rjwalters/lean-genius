import Orbit60
import Certificate_60
namespace Rejection60
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit60.cross g)) := by
  apply Orbit60.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary60.B
  exact SeparatedCanary60.no_joint_literal
end Rejection60
#print axioms Rejection60.no_joint
