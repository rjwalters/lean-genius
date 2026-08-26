import Proofs.Erdos85OneHighCapacityComplementInventory
import Proofs.Erdos85OneHighV2CapacityCover

/-! # Certificate terminal for the partitioned one-high capacity inventory

This is the final composition socket for the H1 certificate campaign.  It
combines checked evidence for the 2,503-row all-even inventory with checked
evidence for its 10,848-row complement, then applies the existing complete
13,351-row capacity cover.
-/

namespace Erdos85

noncomputable section

/-- Checked providers for the two disjoint capacity subinventories combine to
a checked provider for every capacity row. -/
theorem oneHighCapacityInventory_checked_of_partition
    (hAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hNonAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table := by
  intro profile table hcapacity
  rw [oneHighCapacityInventory_mem_iff_allEven_or_nonAllEven] at hcapacity
  rcases hcapacity with hAll | hNon
  · exact hAllEven profile table hAll
  · exact hNonAllEven profile table hNon

/-- The two checked certificate banks close the complete one-high stratum. -/
theorem orderFortyNineStratumExcluded_one_of_capacityPartition_checked
    (hAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hNonAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 :=
  orderFortyNineStratumExcluded_one_of_capacityInventory_checked
    (oneHighCapacityInventory_checked_of_partition hAllEven hNonAllEven)

end

end Erdos85

#print axioms Erdos85.oneHighCapacityInventory_checked_of_partition
#print axioms Erdos85.orderFortyNineStratumExcluded_one_of_capacityPartition_checked
