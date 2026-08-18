import Proofs.Erdos85FiniteDropCapstone
import Proofs.Erdos85Boza48Witness
import Proofs.Erdos85OrderFortyNineDegreeSixWitness

/-!
# Concrete witness inputs for the finite order-49 program

The two existence sides are now checked inside Lean.  The sole remaining
condition for the strict `48 → 49` drop is nonexistence of an order-49
minimum-degree-seven witness, represented separately by the survivor
certificate program.
-/

namespace Erdos85

/-- The order-48 threshold is unconditionally pinned down by the checked
Boza graph and the general counting upper bound. -/
theorem minDegreeForC4_fortyEight_eq_eight_checked :
    minDegreeForC4 48 = 8 :=
  minDegreeForC4_fortyEight_eq_eight boza48_degreeSeven_witness

/-- The checked order-49 graph supplies the unconditional lower bound. -/
theorem seven_le_minDegreeForC4_fortyNine_checked :
    7 ≤ minDegreeForC4 49 := by
  have h := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4
    (n := 49) (d := 6) (by norm_num)).1 orderFortyNine_degreeSix_witness
  omega

/-- Once the seven survivor families are excluded, the checked graphs pin
both thresholds exactly. -/
theorem minDegreeForC4_fortyEight_fortyNine_exact_checked
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=
  minDegreeForC4_fortyEight_fortyNine_exact
    boza48_degreeSeven_witness orderFortyNine_degreeSix_witness hno49

/-- The concrete conditional finite drop.  This remains distinct from the
eventual-monotonicity statement in Erdős Problem 85. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight_checked
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    minDegreeForC4 49 < minDegreeForC4 48 :=
  minDegreeForC4_fortyNine_lt_fortyEight boza48_degreeSeven_witness hno49

end Erdos85
