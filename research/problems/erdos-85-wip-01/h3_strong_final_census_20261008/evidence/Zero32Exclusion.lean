import Zero32Assembly
import Zero32Inputs
namespace Zero32
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  exact threeHighWitnessedColumnCover_no_joint U R Zero32Assembly.pairs
    threeHighColumnScore swaps_valid domains reasons domains_checked table
    Zero32Assembly.cert Zero32Assembly.checked table_no_joint cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 10 58)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 10 58)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 10 58)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross) := by
  rw [← U_eq, ← R_eq] at hc he ⊢
  exact no_joint_literal cross hc he
end Zero32
#print axioms Zero32.no_joint_literal
#print axioms Zero32.no_joint
