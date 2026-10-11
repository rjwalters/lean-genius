import Certificate
import Proofs.Erdos85ThreeHighDistinctBlockPermutationTransport

namespace FullUBlockOrbits
open Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- The retained 55-entry block certificate preserves distinct neighbors. -/
theorem distinct_joint_transport (r : Fin 55) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain (representative r) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighDistinctJointWitness (threeHighEmptyAdj (representative r) R cross)) :
    ∃ cross' : ThreeHighCross,
      cross' ∈ threeHighCrossDomain (representative (target r)) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (representative (target r)) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (representative (target r)) R cross') :=
  threeHighBlockPermutation_distinct_joint_transport _ _ R (label r) (blockLabel r)
    (rows_checked r) (adjacency_checked r) cross hc hExt hJoint

/-- A strong completion at any of the 55 entries survives at one of the
29 checked block targets. This theorem does not exclude any target. -/
theorem distinct_joint_transport_to_targets (r : Fin 55) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain (representative r) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighDistinctJointWitness (threeHighEmptyAdj (representative r) R cross)) :
    ∃ (r' : Fin 55) (cross' : ThreeHighCross), r' ∈ targets ∧
      cross' ∈ threeHighCrossDomain (representative r') R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (representative r') R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (representative r') R cross') := by
  obtain ⟨cross', hc', he', hj'⟩ := distinct_joint_transport r R cross hc hExt hJoint
  exact ⟨target r, cross', target_mem r, hc', he', hj'⟩

end FullUBlockOrbits

#print axioms FullUBlockOrbits.distinct_joint_transport
#print axioms FullUBlockOrbits.distinct_joint_transport_to_targets
