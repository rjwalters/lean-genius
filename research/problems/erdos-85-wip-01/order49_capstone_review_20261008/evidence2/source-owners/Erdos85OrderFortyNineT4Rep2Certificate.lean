import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep2ProofText : String :=
  include_str "Certificates" / "t4_rep2.compact.lrat"

def orderFortyNineT4Rep2Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep2ProofText

theorem orderFortyNineT4Rep2Proof_size :
    orderFortyNineT4Rep2Proof.size = 26081 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep2_check :
    LRAT.check orderFortyNineT4Rep2Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[2]!)) := by
  native_decide

end Erdos85
