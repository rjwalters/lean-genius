import Proofs.Erdos85OrderFortyNineSmallHighProfileMasks
import Proofs.Erdos85OrderFortyNineSmallHighCanonicalCapstone
import Proofs.Erdos85OrderFortyNineThreeHighOneFiber
import Proofs.Erdos85OrderFortyNineThreeHighCnfSemantics
import Proofs.Erdos85OrderFortyNineFiveHighCnfSemantics

/-!
# LRAT exclusion sockets for the canonical small-high representatives

This file connects the classified h=3 and h=5 representative mask arrays to
the semantic CNF bridges.  A checked LRAT proof for any generated canonical
representative therefore directly contradicts the corresponding Boolean
constraints.
-/

namespace Erdos85

open Std Sat
open OrderFortyNineSmallHighCensus

theorem threeHighRepresentativeMasks_high_lsb_zero (index : Nat) :
    OrderFortyNineH3HighMasksZero (threeHighRepresentativeMasks index) := by
  intro a w
  have h := threeHighRepresentativeMasks_high_zero index a
  have hw := congrArg (fun mask : BitVec 9 => mask.getLsbD w.val) h
  simpa [orderFortyNineH3HighVertex] using hw

theorem fiveHighRepresentativeMasks_high_lsb_zero (index : Nat) :
    OrderFortyNineH5HighMasksZero (fiveHighRepresentativeMasks index) := by
  intro a w
  have h := fiveHighRepresentativeMasks_high_zero index a
  have hw := congrArg (fun mask : BitVec 9 => mask.getLsbD w.val) h
  simpa [orderFortyNineH5HighVertex] using hw

theorem false_of_orderFortyNine_threeHighRepresentative_lrat
    {index : Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      (threeHighRepresentativeMasks index) edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedCanonicalSatCnf 3
        (threeHighRepresentativeMasks index))) : False := by
  apply false_of_orderFortyNine_generated_h3_lrat hc
    (threeHighRepresentativeMasks_high_lsb_zero index) proof
  simpa [orderFortyNineGeneratedH3SatCnf_eq_canonical] using hcheck

theorem false_of_orderFortyNine_fiveHighRepresentative_lrat
    {index : Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5
      (fiveHighRepresentativeMasks index) edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedCanonicalSatCnf 5
        (fiveHighRepresentativeMasks index))) : False := by
  apply false_of_orderFortyNine_generated_h5_lrat hc
    (fiveHighRepresentativeMasks_high_lsb_zero index) proof
  simpa [orderFortyNineGeneratedH5SatCnf_eq_canonical] using hcheck

theorem threeHighCanonicalRepresentativeExcluded_of_lrat
    (index : Nat) (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedCanonicalSatCnf 3
        (threeHighRepresentativeMasks index))) :
    ThreeHighCanonicalRepresentativeExcluded index := by
  intro edges hc
  exact false_of_orderFortyNine_threeHighRepresentative_lrat hc proof hcheck

theorem fiveHighCanonicalRepresentativeExcluded_of_lrat
    (index : Nat) (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedCanonicalSatCnf 5
        (fiveHighRepresentativeMasks index))) :
    FiveHighCanonicalRepresentativeExcluded index := by
  intro edges hc
  exact false_of_orderFortyNine_fiveHighRepresentative_lrat hc proof hcheck

theorem orderFortyNineStratumExcluded_three_of_lratChecks
    (hchecks : ∀ index, index ≤ 1 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 3
            (threeHighRepresentativeMasks index))) :
    OrderFortyNineStratumExcluded 3 := by
  apply orderFortyNineStratumExcluded_three_of_representativeExclusions
  intro index hindex
  obtain ⟨proof, hcheck⟩ := hchecks index hindex
  exact threeHighCanonicalRepresentativeExcluded_of_lrat index proof hcheck

theorem orderFortyNineStrataExcluded_smallHigh_of_lratChecks
    (hcover3 : ∀ blocks, blocks ≤ 1 → ThreeHighCanonicalGraphCover blocks)
    (hcover5 : ∀ blocks, blocks ≤ 2 → FiveHighCanonicalGraphCover blocks)
    (hchecks3 : ∀ index, index ≤ 1 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 3
            (threeHighRepresentativeMasks index)))
    (hchecks5 : ∀ index, index ≤ 2 →
      ∃ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
        Std.Tactic.BVDecide.LRAT.check proof
          (orderFortyNineGeneratedCanonicalSatCnf 5
            (fiveHighRepresentativeMasks index))) :
    OrderFortyNineStratumExcluded 3 ∧ OrderFortyNineStratumExcluded 5 := by
  constructor
  · apply orderFortyNineStratumExcluded_three_of_canonical hcover3
    intro index hindex
    obtain ⟨proof, hcheck⟩ := hchecks3 index hindex
    exact threeHighCanonicalRepresentativeExcluded_of_lrat index proof hcheck
  · apply orderFortyNineStratumExcluded_five_of_canonical hcover5
    intro index hindex
    obtain ⟨proof, hcheck⟩ := hchecks5 index hindex
    exact fiveHighCanonicalRepresentativeExcluded_of_lrat index proof hcheck

end Erdos85
