import Orbit69
import Certificate_69
namespace Rejection69
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit69.cross g)) := by
  apply Orbit69.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary69.B
  exact SeparatedCanary69.no_joint_literal
end Rejection69
#print axioms Rejection69.no_joint
