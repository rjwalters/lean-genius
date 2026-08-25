import Proofs.Erdos85OneHighAllEvenSingletonInventory

/-! # Separated repeated keys in the odd one-high profiles

The abstract all-even argument produces two owners of one repeated exchanged
key, but its graph-facing residual originally retained three owner sectors:
equal, root-mate, and genuinely separated.  The exact capacity inventory
shows that profiles one and three always admit a witness in the strongest
sector.  This is a finite statement about the already-verified table and
pairing-refinement enumerators; it does not assert that the residual is
impossible.
-/

namespace Erdos85

/-- A compatible refinement contains the same off-diagonal key in two
distinct source rows which are not a standard mate pair. -/
def OneHighRefinementHasSeparatedRepeatedKey
    (refinement : List (List OneHighLabelPair)) : Prop :=
  ∃ i j : Fin 8,
    i ≠ j ∧ j ≠ oneHighStandardMate i ∧
      ∃ key : OneHighLabelPair,
        key.1 < key.2 ∧
        key ∈ refinement.getD i.val [] ∧
        key ∈ refinement.getD j.val []

instance (refinement : List (List OneHighLabelPair)) :
    Decidable (OneHighRefinementHasSeparatedRepeatedKey refinement) :=
  by
    unfold OneHighRefinementHasSeparatedRepeatedKey
    infer_instance

/-- No profile-one capacity row has an all-even compatible refinement whose
repeated off-diagonal keys are confined to one owner or a root-mate pair. -/
theorem oneHigh_profileOne_allEven_has_separatedRepeatedKey :
    ∀ table ∈ oneHighCapacityInventoryTables 1,
      ∀ refinement ∈ oneHighPairingRefinements 1 table,
        oneHighRefinementAllOffDiagonalEven refinement = true →
          OneHighRefinementHasSeparatedRepeatedKey refinement := by
  native_decide

/-- Profile three has the same strongest-owner-sector conclusion. -/
theorem oneHigh_profileThree_allEven_has_separatedRepeatedKey :
    ∀ table ∈ oneHighCapacityInventoryTables 3,
      ∀ refinement ∈ oneHighPairingRefinements 3 table,
        oneHighRefinementAllOffDiagonalEven refinement = true →
          OneHighRefinementHasSeparatedRepeatedKey refinement := by
  native_decide

end Erdos85
