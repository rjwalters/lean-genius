import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT3Rep3ProofText : String :=
  include_str "Certificates" / "t3_rep3.compact.lrat"

def orderFortyNineT3Rep3Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT3Rep3ProofText

theorem orderFortyNineT3Rep3Proof_size :
    orderFortyNineT3Rep3Proof.size = 29891 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT3Rep3_check :
    LRAT.check orderFortyNineT3Rep3Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[3]!)) := by
  native_decide

end Erdos85
