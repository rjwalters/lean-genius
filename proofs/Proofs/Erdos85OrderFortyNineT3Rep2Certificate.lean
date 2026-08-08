import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT3Rep2ProofText : String :=
  include_str "Certificates" / "t3_rep2.compact.lrat"

def orderFortyNineT3Rep2Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT3Rep2ProofText

theorem orderFortyNineT3Rep2Proof_size :
    orderFortyNineT3Rep2Proof.size = 39363 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT3Rep2_check :
    LRAT.check orderFortyNineT3Rep2Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[2]!)) := by
  native_decide

end Erdos85
