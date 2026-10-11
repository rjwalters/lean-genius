import Orbit45
import Certificate_45
namespace Rejection45
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit45.cross g)) := by
  apply Orbit45.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary45.B
  exact SeparatedCanary45.no_joint_literal
end Rejection45
#print axioms Rejection45.no_joint
