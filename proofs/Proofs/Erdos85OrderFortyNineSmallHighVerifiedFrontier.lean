import Proofs.Erdos85OrderFortyNineSmallHighCnfExclusion

/-!
# Order-49 frontier with canonical small-high LRAT checks

The h=3 and h=5 graph-normalization obligations have been discharged.  This
interface therefore exposes only their five concrete LRAT checks, together
with the independent h=1 and h=7 stratum inputs.
-/

namespace Erdos85

open OrderFortyNineSmallHighCensus

theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks
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
    ¬ C4FreeMinDegreeWitness 49 7 := by
  exact not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata
    h1
    (orderFortyNineStratumExcluded_three_of_lratChecks hchecks3)
    (orderFortyNineStratumExcluded_five_of_lratChecks hchecks5)
    h7

end Erdos85
