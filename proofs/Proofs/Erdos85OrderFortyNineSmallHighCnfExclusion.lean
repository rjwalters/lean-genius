import Proofs.Erdos85OrderFortyNineSmallHighProfileMasks
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

end Erdos85
