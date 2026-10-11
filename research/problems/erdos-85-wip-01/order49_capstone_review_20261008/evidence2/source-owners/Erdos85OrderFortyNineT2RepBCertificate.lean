import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT2RepBProofText : String :=
  include_str "Certificates" / "t2_repB.compact.lrat"

def orderFortyNineT2RepBProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT2RepBProofText

theorem orderFortyNineT2RepBProof_size :
    orderFortyNineT2RepBProof.size = 23565 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT2RepB_check :
    LRAT.check orderFortyNineT2RepBProof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T2Systems[1]!)) := by
  native_decide

end Erdos85
