import Orbit49
import Certificate_49
namespace Rejection49
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit49.cross g)) := by
  apply Orbit49.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary49.B
  exact SeparatedCanary49.no_joint_literal
end Rejection49
#print axioms Rejection49.no_joint
