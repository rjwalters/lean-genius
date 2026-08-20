import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked certificates for the corrected cross-only h512 owner CNF

Both relative sign phases were solved by Kissat with elimination disabled.
`drat-trim` independently verified the traces and emitted zero-RAT LRAT.
The embedded payloads are native-binary LRAT, reproducibly LZ4-compressed
and seven-bit packed for `include_str`.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegFiveOneTwoCrossOnlyS0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof
    (include_str "Certificates" /
      "muneg5_onetwo_crossonly_s0.lz4pack")
    3146751 5636906

def muNegFiveOneTwoCrossOnlyS1Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof
    (include_str "Certificates" /
      "muneg5_onetwo_crossonly_s1.lz4pack")
    3398180 5918100

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveOneTwoCrossOnlyOwner_check_s0 :
    LRAT.check muNegFiveOneTwoCrossOnlyS0Proof
      (muNegFiveOneTwoCrossOnlyOwnerSatCnf false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveOneTwoCrossOnlyOwner_check_s1 :
    LRAT.check muNegFiveOneTwoCrossOnlyS1Proof
      (muNegFiveOneTwoCrossOnlyOwnerSatCnf true) := by
  native_decide

theorem muNegFiveOneTwoCrossOnlyOwner_unsat (sigma : Bool) :
    (muNegFiveOneTwoCrossOnlyOwnerSatCnf sigma).Unsat := by
  cases sigma
  · exact LRAT.check_sound _ _ muNegFiveOneTwoCrossOnlyOwner_check_s0
  · exact LRAT.check_sound _ _ muNegFiveOneTwoCrossOnlyOwner_check_s1

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwner_check_s0
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwner_check_s1
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwner_unsat
