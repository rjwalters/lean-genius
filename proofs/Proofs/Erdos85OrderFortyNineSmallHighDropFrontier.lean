import Proofs.Erdos85OrderFortyNineSmallHighVerifiedFrontier
import Proofs.Erdos85FiniteDropWitnesses

/-!
# Concrete order-48/order-49 drop from the small-high LRAT frontier

The order-48 degree-seven witness and order-49 degree-six witness are already
checked in Lean.  Combining them with the order-49 exclusion interface pins
both threshold values and proves the strict finite drop.
-/

namespace Erdos85

open OrderFortyNineSmallHighCensus

theorem minDegreeForC4_fortyEight_fortyNine_exact_of_smallHighLratChecks
    (h1 : OrderFortyNineStratumExcluded 1)
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
    (h7 : OrderFortyNineStratumExcluded 7) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 := by
  apply minDegreeForC4_fortyEight_fortyNine_exact_checked
  exact not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks
    h1 hchecks3 hchecks5 h7

theorem minDegreeForC4_fortyNine_lt_fortyEight_of_smallHighLratChecks
    (h1 : OrderFortyNineStratumExcluded 1)
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
    (h7 : OrderFortyNineStratumExcluded 7) :
    minDegreeForC4 49 < minDegreeForC4 48 := by
  have hexact :=
    minDegreeForC4_fortyEight_fortyNine_exact_of_smallHighLratChecks
      h1 hchecks3 hchecks5 h7
  omega

end Erdos85
