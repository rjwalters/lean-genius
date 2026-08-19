import Proofs.Erdos85MuNegThreeOneTwoOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85
open Std.Tactic.BVDecide

def muNegThreeFwdC0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_onetwo_fix_s0_fwd_c0.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeOneTwoOwner_check_fwd_c0 :
    LRAT.check muNegThreeFwdC0Proof (muNegThreeOneTwoOwnerSatCnf true 0) := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwner_check_fwd_c0
