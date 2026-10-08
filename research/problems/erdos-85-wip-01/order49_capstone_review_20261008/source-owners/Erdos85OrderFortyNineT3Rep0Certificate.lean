import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT3Rep0ProofText : String :=
  include_str "Certificates" / "t3_rep0.compact.lrat"

def orderFortyNineT3Rep0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT3Rep0ProofText

theorem orderFortyNineT3Rep0Proof_size :
    orderFortyNineT3Rep0Proof.size = 15532 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT3Rep0_check :
    LRAT.check orderFortyNineT3Rep0Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[0]!)) := by
  native_decide

end Erdos85
