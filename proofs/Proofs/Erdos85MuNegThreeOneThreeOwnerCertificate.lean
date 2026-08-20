import Proofs.Erdos85MuNegThreeOneThreeOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! Independently compiled LRAT terminals for the μ=-3 `(1,3)`
owner-grid endpoint, both sign phases (kissat `--plain`, drat-trim
pure-RUP `0 RAT lemmas` + `s VERIFIED`, lrat-check verified,
compacted). -/

namespace Erdos85

open Std.Tactic.BVDecide

def muNegThreeOneThreeS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_onethree_s0.compact.lrat")

def muNegThreeOneThreeS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_onethree_s1.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeOneThreeOwner_check_s0 :
    LRAT.check muNegThreeOneThreeS0Proof
      (muNegThreeOneThreeOwnerSatCnf false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeOneThreeOwner_check_s1 :
    LRAT.check muNegThreeOneThreeS1Proof
      (muNegThreeOneThreeOwnerSatCnf true) := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegThreeOneThreeOwner_check_s0
#print axioms Erdos85.muNegThreeOneThreeOwner_check_s1
