import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep4ProofText : String :=
  include_str "Certificates" / "t4_rep4.compact.lrat"

def orderFortyNineT4Rep4Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep4ProofText

theorem orderFortyNineT4Rep4Proof_size :
    orderFortyNineT4Rep4Proof.size = 24704 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep4_check :
    LRAT.check orderFortyNineT4Rep4Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[4]!)) := by
  native_decide

end Erdos85
