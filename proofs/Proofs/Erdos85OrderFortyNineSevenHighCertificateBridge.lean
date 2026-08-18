import Proofs.Erdos85OrderFortyNineSevenHighCnfSemantics
import Proofs.Erdos85OrderFortyNineSevenHighGraphCover

/-! # LRAT-to-graph bridge for canonical seven-high representatives -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem sevenHighCanonicalRepresentativeExcluded_of_lrat
    (blocks index : Nat)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks blocks index))) :
    SevenHighCanonicalRepresentativeExcluded blocks index := by
  intro edges hc
  exact false_of_orderFortyNine_generated_h7_lrat hc
    (representativeMasks_h7_high_zero blocks index) proof hcheck

theorem orderFortyNineStratumExcluded_seven_of_lratChecks
    (hchecks : ∀ blocks index, blocks ≤ 7 →
      index < (OrderFortyNineSevenHighCensus.reps blocks).length →
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedH7SatCnf
            (OrderFortyNineSevenHighCensus.representativeMasks blocks index))) :
    OrderFortyNineStratumExcluded 7 := by
  apply orderFortyNineStratumExcluded_seven_of_certificates
  intro blocks index hblocks hindex
  obtain ⟨proof, hcheck⟩ := hchecks blocks index hblocks hindex
  exact sevenHighCanonicalRepresentativeExcluded_of_lrat
    blocks index proof hcheck

end Erdos85
