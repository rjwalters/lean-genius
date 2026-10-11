import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT3Rep1ProofText : String :=
  include_str "Certificates" / "t3_rep1.compact.lrat"

def orderFortyNineT3Rep1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT3Rep1ProofText

theorem orderFortyNineT3Rep1Proof_size :
    orderFortyNineT3Rep1Proof.size = 7495 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT3Rep1_check :
    LRAT.check orderFortyNineT3Rep1Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[1]!)) := by
  native_decide

end Erdos85
