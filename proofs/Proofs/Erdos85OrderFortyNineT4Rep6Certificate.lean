import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep6ProofText : String :=
  include_str "Certificates" / "t4_rep6.compact.lrat"

def orderFortyNineT4Rep6Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep6ProofText

theorem orderFortyNineT4Rep6Proof_size :
    orderFortyNineT4Rep6Proof.size = 20231 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep6_check :
    LRAT.check orderFortyNineT4Rep6Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[6]!)) := by
  native_decide

end Erdos85
