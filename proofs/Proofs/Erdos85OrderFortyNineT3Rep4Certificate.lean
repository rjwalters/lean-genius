import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT3Rep4ProofText : String :=
  include_str "Certificates" / "t3_rep4.compact.lrat"

def orderFortyNineT3Rep4Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT3Rep4ProofText

theorem orderFortyNineT3Rep4Proof_size :
    orderFortyNineT3Rep4Proof.size = 19621 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT3Rep4_check :
    LRAT.check orderFortyNineT3Rep4Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[4]!)) := by
  native_decide

end Erdos85
