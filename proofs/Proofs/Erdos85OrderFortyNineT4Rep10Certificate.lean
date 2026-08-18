import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT4Rep10ProofText : String :=
  include_str "Certificates" / "t4_rep10.compact.lrat"

def orderFortyNineT4Rep10Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT4Rep10ProofText

theorem orderFortyNineT4Rep10Proof_size :
    orderFortyNineT4Rep10Proof.size = 22980 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT4Rep10_check :
    LRAT.check orderFortyNineT4Rep10Proof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[10]!)) := by
  native_decide

end Erdos85
