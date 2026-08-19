import Proofs.Erdos85MuNegThreeOneTwoOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85
open Std.Tactic.BVDecide

def muNegThreeRevC6Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_onetwo_fix_s0_rev_c6.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeOneTwoOwner_check_rev_c6 :
    LRAT.check muNegThreeRevC6Proof (muNegThreeOneTwoOwnerSatCnf false 6) := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwner_check_rev_c6
