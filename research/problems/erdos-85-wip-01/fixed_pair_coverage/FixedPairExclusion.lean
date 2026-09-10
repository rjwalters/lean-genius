import CoverageAssembly
import Inputs
import TableRejections
import Proofs.Erdos85ThreeHighWitnessedColumnCover

namespace ColumnCoverageFixedPair
open Erdos85 ColumnCoverageLiterals
attribute [local irreducible] threeHighCrossDomain

theorem no_joint_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  exact threeHighWitnessedColumnCover_no_joint U R ColumnCoverageAssembly.pairs
    threeHighColumnScore ColumnCoverageInputs.swaps_valid domains
    ColumnCoverageDomains.reasons ColumnCoverageDomains.checked table
    ColumnCoverageAssembly.cert ColumnCoverageAssembly.checked table_no_joint cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross) := by
  rw [← U_eq, ← R_eq] at hc he ⊢
  exact no_joint_literal cross hc he
end ColumnCoverageFixedPair
#print axioms ColumnCoverageFixedPair.no_joint_literal
#print axioms ColumnCoverageFixedPair.no_joint
