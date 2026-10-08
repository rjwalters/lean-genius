import Proofs.Erdos85OrderFortyNineCapstone
import Proofs.Erdos85H3Stratum

/-!
# Order-49 capstone with the three-high stratum discharged

The accepted three-high and five-high stratum theorems leave two explicit
external evidence hypotheses: the one-high checked capacity inventory and
the seven-high structural `hsb` cover-and-leaf evidence. The conclusions
remain conditional on those hypotheses; this is not an unconditional Lean
proof of the finite drop or a resolution of the full Erdős problem.
-/

namespace Erdos85

/-- The order-49 upper bound, conditional only on one-high and seven-high
external evidence. The three-high stratum is discharged by its theorem. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
    hOne depth hSeven H3.orderFortyNineStratumExcluded_three

/-- Exact thresholds from the same two evidence hypotheses and the checked
order-48 and order-49 lower-bound witnesses. -/
theorem minDegreeForC4_fortyEight_fortyNine_exact_of_h1_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=
  minDegreeForC4_fortyEight_fortyNine_exact_checked
    (not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence hOne depth hSeven)

/-- The strict finite drop, conditional on the same two evidence hypotheses. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight_of_h1_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    minDegreeForC4 49 < minDegreeForC4 48 :=
  minDegreeForC4_fortyNine_lt_fortyEight_checked
    (not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence hOne depth hSeven)

end Erdos85

#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence
#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_of_h1_h7Evidence
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_of_h1_h7Evidence
