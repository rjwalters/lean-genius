import Proofs.Erdos85OneHighAllEvenCapacityInventory
import Proofs.Erdos85OneHighStructuralTerminalInterface

/-! # Stratum socket for the all-even capacity inventory

The ordinary structural capstone may choose any raw one-high presentation,
whereas the orbit cover also chooses the presentation whose table agrees with
a stored representative.  This file makes those choices once: it runs the
structural split on the capacity-covered presentation and sends only its
all-even branch to the 2,503-row filtered certificate inventory.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Checked UNSAT evidence for the exact all-even capacity inventory, together
with the other three structural terminals, excludes the complete one-high
stratum. -/
theorem orderFortyNineStratumExcluded_one_of_allEvenCapacity_checked
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hturn : OneHighThreePairTurnSectorExcluded)
    (hcross : OneHighCrossBlockSectorExcluded) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, stored, hstored, hagree⟩ :=
    oneHighRawV2OrbitCover_capacityInventory G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  rcases orderFortyNine_oneHigh_structural_sector_capstone
      G hfree hmin (Fintype.card_fin 49) hv p with
    heven | hmate | hthree | hfour
  · let profile : Fin 5 :=
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
    have hstoredAll : stored ∈
        oneHighAllEvenCapacityInventoryTables profile :=
      oneHigh_storedTable_mem_allEvenCapacityInventory
        G hfree hv p heven stored hstored hagree
    have hcertStored : OneHighFamilyV2CheckedUnsat p.profile stored :=
      hchecked profile stored hstoredAll
    have hcertGraph : OneHighFamilyV2CheckedUnsat p.profile
        (oneHighFamilyGraphTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v
              p.branchLabel p.leafLabel)) p.profile) :=
      hcertStored.transport hagree.symm
    exact false_of_rawOneHigh_v2Checked
      G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
        p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
        p.branch_mate p.leafLabel p.profile p.constraints hcertGraph
  · exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hmate
  · exact hturn G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hthree
  · exact hcross G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hfour

end

end Erdos85
