import Orbit24
import Certificate_24
namespace Rejection24
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit24.cross g)) := by
  apply Orbit24.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary24.B
  exact SeparatedCanary24.no_joint_literal
end Rejection24
#print axioms Rejection24.no_joint
