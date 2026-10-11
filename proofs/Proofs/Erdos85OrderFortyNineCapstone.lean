import Proofs.Erdos85OneHighV2CapacityCover
import Proofs.Erdos85H3PairCell
import Proofs.Erdos85H5Stratum
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbStratumCapstone
import Proofs.Erdos85OrderFortyNineStrataCapstone
import Proofs.Erdos85FiniteDropWitnesses

/-!
# Order-49 integration capstone

This module assembles the order-49 upper bound `¬ C4FreeMinDegreeWitness 49 7`
from the stratum developments.  The case split over the number `h` of
degree-eight vertices (`h = 1, 3, 5, 7, 9`) is
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata`; `h = 9` is closed
inside that theorem.

Discharged here by proved theorems (no hypothesis):

* `h = 5`: `Erdos85.H5.orderFortyNineStratumExcluded_five`;
* `h = 3`, pair cell `t = 0`:
  `Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero`.

Left as explicit hypotheses (external evidence, NOT proved in Lean):

* `hOne`: checked UNSAT evidence for every row of the 13,351-row one-high
  capacity inventory, in the shape wanted by
  `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`;
* `hSeven`: `hsb<depth>` evidence (checked cover and leaves) for the 28
  structural seven-high `t = 0` cubes, in the shape wanted by
  `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence`;
* `hThreeOne`: the three-high triple cell `OrderFortyNineTripleCellExcluded 3 1`.

The theorems below are therefore conditional statements.  They are not a Lean
proof of `f(49) = 7`.
-/

namespace Erdos85

/-- Order-49 capstone in stratum form for `h = 3`: the three-high stratum is
taken whole.  This is the socket for an eventual proved
`OrderFortyNineStratumExcluded 3`. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex)
    (hThree : OrderFortyNineStratumExcluded 3) :
    ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata
    (orderFortyNineStratumExcluded_one_of_capacityInventory_checked hOne)
    hThree
    H5.orderFortyNineStratumExcluded_five
    (orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence depth hSeven)

/-- **Order-49 capstone.**  No `C₄`-free graph on 49 vertices has minimum
degree at least seven, given three pieces of external evidence: the one-high
checked inventory, the seven-high `hsb` evidence, and the three-high triple
cell `t = 1`.  The five-high stratum and the three-high pair cell `t = 0` are
discharged by proved theorems. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex)
    (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
    hOne depth hSeven
    (orderFortyNineStratumExcluded_three_of_tripleCells
      H3Pair.orderFortyNineTripleCellExcluded_three_zero hThreeOne)

/-- Exact thresholds `f(48) = 8` and `f(49) = 7` from the same three pieces of
external evidence.  The lower sides are the checked Boza order-48 graph and
the checked order-49 degree-six graph. -/
theorem minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex)
    (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=
  minDegreeForC4_fortyEight_fortyNine_exact_checked
    (not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
      hOne depth hSeven hThreeOne)

/-- The strict finite drop `f(49) < f(48)` from the same external evidence. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex)
    (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    minDegreeForC4 49 < minDegreeForC4 48 :=
  minDegreeForC4_fortyNine_lt_fortyEight_checked
    (not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
      hOne depth hSeven hThreeOne)

end Erdos85

#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence
