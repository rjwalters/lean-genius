import Proofs.Erdos85OneHighV2InventoryCover

/-!
# Cross-miss-capacity pruning of the one-high inventory

The raw inventory classifies symmetric miss tables with the prescribed row
sums.  Graph geometry supplies the additional F3b capacity inequality
`m(c,mate j) + m(j,mate c) ≤ 5`.  This file makes the corresponding finite
subinventory kernel-readable and records its exact size.
-/

namespace Erdos85

/-- Executable form of the cross-miss capacity inequality on all 24
non-mate unordered branch pairs.  `oneHighFamilyTableGet` normalizes both
read coordinates to the stored upper-triangular convention. -/
def oneHighTableCrossMissCapacity (table : OneHighMissTable) : Bool :=
  oneHighFamilyTablePairs.all fun pair =>
    decide (oneHighFamilyTableGet table pair.1 (pair.2 ^^^ 1) +
      oneHighFamilyTableGet table pair.2 (pair.1 ^^^ 1) ≤ 5)

/-- The authoritative orbit inventory after the graph-side capacity filter. -/
def oneHighCapacityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighInventoryTables profile).filter oneHighTableCrossMissCapacity

theorem oneHighCapacityInventoryTables_length_zero :
    (oneHighCapacityInventoryTables 0).length = 1485 := by native_decide

theorem oneHighCapacityInventoryTables_length_one :
    (oneHighCapacityInventoryTables 1).length = 3617 := by native_decide

theorem oneHighCapacityInventoryTables_length_two :
    (oneHighCapacityInventoryTables 2).length = 4717 := by native_decide

theorem oneHighCapacityInventoryTables_length_three :
    (oneHighCapacityInventoryTables 3).length = 2693 := by native_decide

theorem oneHighCapacityInventoryTables_length_four :
    (oneHighCapacityInventoryTables 4).length = 839 := by native_decide

/-- The capacity filter retains exactly 13,351 of the 13,541 orbit rows. -/
theorem oneHighCapacityInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighCapacityInventoryTables profile).length).sum = 13351 := by
  native_decide

/-- Exactly 190 raw inventory representatives violate graph-side capacity. -/
theorem oneHighCapacityInventory_removed_count :
    oneHighInventoryRows.length -
      ((List.finRange 5).map fun profile =>
        (oneHighCapacityInventoryTables profile).length).sum = 190 := by
  native_decide

end Erdos85
