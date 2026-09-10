import Orbit8
import Certificate_08
namespace Rejection8
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit8.cross g)) := by
  apply Orbit8.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary8.B
  exact SeparatedCanary8.no_joint_literal
end Rejection8
#print axioms Rejection8.no_joint
