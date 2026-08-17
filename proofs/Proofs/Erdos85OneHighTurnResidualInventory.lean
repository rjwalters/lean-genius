import Proofs.Erdos85OneHighTurnParityReflection

/-! # Turn residual after removing mate-key and cross-block parity sectors -/

namespace Erdos85

/-- Exact same-owner odd turn carried by a parity state that has neither an
odd standard-mate key nor an odd alternating cross block. -/
def oneHighTableHasSaturatedOddTurnResidualByParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let choices := List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) source
  (List.ofFn fun source : Fin 8 => source).any fun source =>
    let rows := choices[source.val]!.filter fun row =>
      !(oneHighSaturatedTurnRowTriples source row).isEmpty
    !rows.isEmpty &&
      rows.any fun row =>
        let triples := oneHighSaturatedTurnRowTriples source row
        (oneHighPairingParityStatesWithSourceRowChoices
          choices source row).any fun mask =>
          !oneHighParityMaskHasOddMateKey mask &&
            !oneHighParityMaskHasOddCrossBlock mask &&
            triples.any fun triple =>
              oneHighParityMaskOdd mask triple.1 triple.2.1 &&
                oneHighParityMaskOdd mask triple.2.1 triple.2.2

def oneHighSaturatedOddTurnResidualInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasSaturatedOddTurnResidualByParity profile.val)

/-- Removing the mate-key and cross-block overlaps cuts the odd-turn inventory
from 9,707 to 7,433 representatives. -/
theorem oneHighSaturatedOddTurnResidualInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighSaturatedOddTurnResidualInventoryTables profile).length) =
      [987, 2347, 2533, 1282, 284] := by
  native_decide

theorem oneHighSaturatedOddTurnResidualInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighSaturatedOddTurnResidualInventoryTables profile).length).sum =
      7433 := by
  rw [oneHighSaturatedOddTurnResidualInventory_profile_lengths]
  norm_num

end Erdos85
