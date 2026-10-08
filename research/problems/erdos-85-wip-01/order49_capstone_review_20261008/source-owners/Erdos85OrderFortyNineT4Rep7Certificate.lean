import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep7ProofText : String :=
  include_str "Certificates" / "t4_rep7.compact.lrat"

def orderFortyNineT4Rep7Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep7ProofText

theorem orderFortyNineT4Rep7Proof_size :
    orderFortyNineT4Rep7Proof.size = 21091 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep7_check :
    LRAT.check orderFortyNineT4Rep7Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[7]!)) := by
  native_decide

end Erdos85
