import Proofs.Erdos85OrderFortyNineCapstoneH3
import Proofs.Erdos85OneHighV2InventoryNonzero

/-!
# Order-49 capstone with the H1 hypothesis reduced to unsatisfiability

The released capstones (`Erdos85OrderFortyNineCapstoneH3`, unchanged) take the
one-high hypothesis `hOne` in the form `OneHighFamilyV2CheckedUnsat`, which
bundles a `nonzero` field (no literal `0` in the generated DIMACS clauses)
with the `unsat` field.  `Erdos85OneHighV2InventoryNonzero` proves `nonzero`
structurally for every table, so the three theorems below restate the
capstones with `hOne` weakened to the unsatisfiability statement alone.  The
conclusions, the `depth`/`hSeven` hypotheses, and the remaining conditionality
are unchanged: these are still conditional statements, not an unconditional
Lean proof of the finite drop.

New module; it changes no existing module.
-/

namespace Erdos85

/-- `not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence` with the
one-high hypothesis reduced to unsatisfiability of each inventory CNF. -/
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1Unsat_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        ∀ assignment : Nat → Bool,
          ¬(oneHighFamilyV2SatCnf profile.val table).Sat assignment)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence
    (oneHighCapacityInventory_checked_of_unsat hOne) depth hSeven

/-- `minDegreeForC4_fortyEight_fortyNine_exact_of_h1_h7Evidence` with the
one-high hypothesis reduced to unsatisfiability. -/
theorem minDegreeForC4_fortyEight_fortyNine_exact_of_h1Unsat_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        ∀ assignment : Nat → Bool,
          ¬(oneHighFamilyV2SatCnf profile.val table).Sat assignment)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=
  minDegreeForC4_fortyEight_fortyNine_exact_of_h1_h7Evidence
    (oneHighCapacityInventory_checked_of_unsat hOne) depth hSeven

/-- `minDegreeForC4_fortyNine_lt_fortyEight_of_h1_h7Evidence` with the
one-high hypothesis reduced to unsatisfiability. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight_of_h1Unsat_h7Evidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        ∀ assignment : Nat → Bool,
          ¬(oneHighFamilyV2SatCnf profile.val table).Sat assignment)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    minDegreeForC4 49 < minDegreeForC4 48 :=
  minDegreeForC4_fortyNine_lt_fortyEight_of_h1_h7Evidence
    (oneHighCapacityInventory_checked_of_unsat hOne) depth hSeven

end Erdos85

#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1Unsat_h7Evidence
#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_of_h1Unsat_h7Evidence
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_of_h1Unsat_h7Evidence
