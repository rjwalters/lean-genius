import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep5ProofText : String :=
  include_str "Certificates" / "t4_rep5.compact.lrat"

def orderFortyNineT4Rep5Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep5ProofText

theorem orderFortyNineT4Rep5Proof_size :
    orderFortyNineT4Rep5Proof.size = 11114 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep5_check :
    LRAT.check orderFortyNineT4Rep5Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[5]!)) := by
  native_decide

end Erdos85
