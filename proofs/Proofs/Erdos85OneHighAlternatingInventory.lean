import Proofs.Erdos85OneHighV2CapacityInventory

/-! # Executable inventory filter for the alternating odd C4 sector -/

namespace Erdos85

/-- An inventory table contains an alternating odd label C4 when two distinct
standard mate-pairs span a `2 × 2` block of odd exchanged multiplicities. -/
def oneHighTableHasAlternatingOddC4 (table : OneHighMissTable) : Bool :=
  (List.range 4).any fun p =>
    (List.range 4).any fun q =>
      p < q &&
      decide (oneHighFamilyTableGet table (2 * p) (2 * q) % 2 = 1) &&
      decide (oneHighFamilyTableGet table (2 * p) (2 * q + 1) % 2 = 1) &&
      decide (oneHighFamilyTableGet table (2 * p + 1) (2 * q) % 2 = 1) &&
      decide (oneHighFamilyTableGet table (2 * p + 1) (2 * q + 1) % 2 = 1)

/-- Raw alternating-C4 subinventory, prior to graph-side capacity pruning. -/
def oneHighAlternatingInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighInventoryTables profile).filter oneHighTableHasAlternatingOddC4

/-- Alternating-C4 subinventory after graph-side cross-miss capacity pruning. -/
def oneHighCapacityAlternatingInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    oneHighTableHasAlternatingOddC4

theorem oneHighAlternatingInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighAlternatingInventoryTables profile).length) =
      [138, 222, 263, 101, 25] := by
  native_decide

theorem oneHighAlternatingInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighAlternatingInventoryTables profile).length).sum = 749 := by
  native_decide

theorem oneHighCapacityAlternatingInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighCapacityAlternatingInventoryTables profile).length) =
      [130, 220, 253, 101, 24] := by
  native_decide

theorem oneHighCapacityAlternatingInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighCapacityAlternatingInventoryTables profile).length).sum = 728 := by
  native_decide

/-- Capacity pruning removes 21 alternating-C4 orbit representatives. -/
theorem oneHighCapacityAlternatingInventory_removed_count :
    ((List.finRange 5).map fun profile =>
      (oneHighAlternatingInventoryTables profile).length).sum -
      ((List.finRange 5).map fun profile =>
        (oneHighCapacityAlternatingInventoryTables profile).length).sum = 21 := by
  native_decide

end Erdos85
