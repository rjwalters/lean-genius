import Proofs.Erdos85OrderFortyNineCapstone

/-!
# Axiom audit of the order-49 capstone ingredients

No declarations.  This module prints the axiom set of each ingredient of
`Erdos85OrderFortyNineCapstone`, so that every axiom of the capstone can be
attributed to the stratum development it comes from.
-/

-- Case split and the internally closed nine-high stratum.
#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata
#print axioms Erdos85.orderFortyNineStratumExcluded_nine
#print axioms Erdos85.orderFortyNineStratumExcluded_three_of_tripleCells
-- One-high reduction (conditional on checked evidence).
#print axioms Erdos85.orderFortyNineStratumExcluded_one_of_capacityInventory_checked
-- Three-high pair cell.
#print axioms Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero
-- Five-high stratum.
#print axioms Erdos85.H5.orderFortyNineStratumExcluded_five
-- Seven-high stratum (conditional on hsb evidence).
#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence
-- Lower-side witnesses.
#print axioms Erdos85.boza48_degreeSeven_witness
#print axioms Erdos85.orderFortyNine_degreeSix_witness
-- The capstone statements.
#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
#print axioms Erdos85.not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
#print axioms Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence
#print axioms Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence
