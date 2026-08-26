import Proofs.Erdos85OneHighCapacityPartitionTerminal
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalTerminal
import Proofs.Erdos85OrderFortyNineSmallHighDropFrontier

/-!
# Order-49 drop frontier with partitioned H1 and canonical H7 inputs

This is the integration socket matching the two active certificate campaigns.
The H1 side is split into the all-even and complementary capacity inventories;
the H7 side is the canonical zero-triple completion exclusion.  The already
normalized H3/H5 strata retain their five concrete LRAT inputs.
-/

namespace Erdos85

open OrderFortyNineSmallHighCensus

/-- The active H1/H7 certificate interfaces, together with the five H3/H5
checks, pin the two finite extremal values. -/
theorem minDegreeForC4_fortyEight_fortyNine_exact_of_partitionedCanonicalChecks
    (hAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hNonAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hchecks3 : ∀ index, index ≤ 1 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 3
            (threeHighRepresentativeMasks index)))
    (hchecks5 : ∀ index, index ≤ 2 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 5
            (fiveHighRepresentativeMasks index)))
    (h7zero : SevenHighT0CanonicalCompletionExcluded) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 := by
  apply minDegreeForC4_fortyEight_fortyNine_exact_of_smallHighLratChecks
  · exact orderFortyNineStratumExcluded_one_of_capacityPartition_checked
      hAllEven hNonAllEven
  · exact hchecks3
  · exact hchecks5
  · exact orderFortyNineStratumExcluded_seven_of_canonicalCompletion h7zero

/-- Consequently the checked campaign interfaces prove the strict drop from
order 48 to order 49. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight_of_partitionedCanonicalChecks
    (hAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hNonAllEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hchecks3 : ∀ index, index ≤ 1 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 3
            (threeHighRepresentativeMasks index)))
    (hchecks5 : ∀ index, index ≤ 2 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 5
            (fiveHighRepresentativeMasks index)))
    (h7zero : SevenHighT0CanonicalCompletionExcluded) :
    minDegreeForC4 49 < minDegreeForC4 48 := by
  have hexact :=
    minDegreeForC4_fortyEight_fortyNine_exact_of_partitionedCanonicalChecks
      hAllEven hNonAllEven hchecks3 hchecks5 h7zero
  omega

end Erdos85

#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_of_partitionedCanonicalChecks
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_of_partitionedCanonicalChecks
