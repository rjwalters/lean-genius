import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep8ProofText : String :=
  include_str "Certificates" / "t4_rep8.compact.lrat"

def orderFortyNineT4Rep8Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep8ProofText

theorem orderFortyNineT4Rep8Proof_size :
    orderFortyNineT4Rep8Proof.size = 31401 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep8_check :
    LRAT.check orderFortyNineT4Rep8Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[8]!)) := by
  native_decide

end Erdos85
