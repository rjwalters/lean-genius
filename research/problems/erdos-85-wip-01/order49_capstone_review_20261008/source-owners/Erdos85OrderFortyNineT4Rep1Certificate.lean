import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep1ProofText : String :=
  include_str "Certificates" / "t4_rep1.compact.lrat"

def orderFortyNineT4Rep1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep1ProofText

theorem orderFortyNineT4Rep1Proof_size :
    orderFortyNineT4Rep1Proof.size = 55481 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep1_check :
    LRAT.check orderFortyNineT4Rep1Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[1]!)) := by
  native_decide

end Erdos85
