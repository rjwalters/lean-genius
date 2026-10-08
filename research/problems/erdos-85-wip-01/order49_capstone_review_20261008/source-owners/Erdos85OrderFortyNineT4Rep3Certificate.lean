import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep3ProofText : String :=
  include_str "Certificates" / "t4_rep3.compact.lrat"

def orderFortyNineT4Rep3Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep3ProofText

theorem orderFortyNineT4Rep3Proof_size :
    orderFortyNineT4Rep3Proof.size = 26674 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep3_check :
    LRAT.check orderFortyNineT4Rep3Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[3]!)) := by
  native_decide

end Erdos85
