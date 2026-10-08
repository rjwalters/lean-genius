import Orbit63
import Certificate_63
namespace Rejection63
open Erdos85
theorem no_joint (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (Orbit63.cross g)) := by
  apply Orbit63.no_joint_cross
  change ¬ ThreeHighJointWitness SeparatedCanary63.B
  exact SeparatedCanary63.no_joint_literal
end Rejection63
#print axioms Rejection63.no_joint
