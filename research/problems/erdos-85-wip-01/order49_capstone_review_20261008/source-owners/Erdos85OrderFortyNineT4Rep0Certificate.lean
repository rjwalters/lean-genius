import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep0ProofText : String :=
  include_str "Certificates" / "t4_rep0.compact.lrat"

def orderFortyNineT4Rep0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep0ProofText

theorem orderFortyNineT4Rep0Proof_size :
    orderFortyNineT4Rep0Proof.size = 39866 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep0_check :
    LRAT.check orderFortyNineT4Rep0Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[0]!)) := by
  native_decide

end Erdos85
