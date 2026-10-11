import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep9ProofText : String :=
  include_str "Certificates" / "t4_rep9.compact.lrat"

def orderFortyNineT4Rep9Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep9ProofText

theorem orderFortyNineT4Rep9Proof_size :
    orderFortyNineT4Rep9Proof.size = 25958 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep9_check :
    LRAT.check orderFortyNineT4Rep9Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[9]!)) := by
  native_decide

end Erdos85
