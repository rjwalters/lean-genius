import Zero26Assembly
import Zero26Inputs
namespace Zero26
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  exact threeHighWitnessedColumnCover_no_joint U R Zero26Assembly.pairs
    threeHighColumnScore swaps_valid domains reasons domains_checked table
    Zero26Assembly.cert Zero26Assembly.checked table_no_joint cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross) := by
  rw [← U_eq, ← R_eq] at hc he ⊢
  exact no_joint_literal cross hc he
end Zero26
#print axioms Zero26.no_joint_literal
#print axioms Zero26.no_joint
