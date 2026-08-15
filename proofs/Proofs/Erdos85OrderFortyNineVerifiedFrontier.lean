import Proofs.Erdos85OneHighV2CapacityCover
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Verified order-49 frontier

This is the theorem-backed obligation ledger for excluding an order-49
minimum-degree-seven witness.  The one-high input ranges only over the
capacity-compatible exact-v2 inventory; the remaining inputs are exactly the
thirteen triple-incidence cells in the three-, five-, and seven-high strata.

No non-one-high cell is recorded as closed here until its semantic exclusion
is available as an inhabitant of `OrderFortyNineTripleCellExcluded`.
-/

namespace Erdos85

/-- The exact currently verified certificate interface for the order-49
exclusion: 13,351 filtered one-high rows and thirteen non-one-high cells. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_verifiedFrontier
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (h30 : OrderFortyNineTripleCellExcluded 3 0)
    (h31 : OrderFortyNineTripleCellExcluded 3 1)
    (h50 : OrderFortyNineTripleCellExcluded 5 0)
    (h51 : OrderFortyNineTripleCellExcluded 5 1)
    (h52 : OrderFortyNineTripleCellExcluded 5 2)
    (h70 : OrderFortyNineTripleCellExcluded 7 0)
    (h71 : OrderFortyNineTripleCellExcluded 7 1)
    (h72 : OrderFortyNineTripleCellExcluded 7 2)
    (h73 : OrderFortyNineTripleCellExcluded 7 3)
    (h74 : OrderFortyNineTripleCellExcluded 7 4)
    (h75 : OrderFortyNineTripleCellExcluded 7 5)
    (h76 : OrderFortyNineTripleCellExcluded 7 6)
    (h77 : OrderFortyNineTripleCellExcluded 7 7) :
    ¬ C4FreeMinDegreeWitness 49 7 := by
  exact not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata
    (orderFortyNineStratumExcluded_one_of_capacityInventory_checked hchecked)
    (orderFortyNineStratumExcluded_three_of_tripleCells h30 h31)
    (orderFortyNineStratumExcluded_five_of_tripleCells h50 h51 h52)
    (orderFortyNineStratumExcluded_seven_of_tripleCells
      h70 h71 h72 h73 h74 h75 h76 h77)

end Erdos85
