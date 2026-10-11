import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT certificate for the first order-49 two-triple profile

The certificate text is generated from the manifest-pinned external LRAT by
renumbering derived clauses densely and dropping an optional leading deletion
of original clauses.  `include_str` makes the exact certificate bytes an input
to this module; Std's pure parser and checker then verify them.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def orderFortyNineT2RepAProofText : String :=
  include_str "Certificates" / "t2_repA.compact.lrat"

def orderFortyNineT2RepAProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof orderFortyNineT2RepAProofText

theorem orderFortyNineT2RepAProof_size :
    orderFortyNineT2RepAProof.size = 9145 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orderFortyNineT2RepA_check :
    LRAT.check orderFortyNineT2RepAProof
      (orderFortyNineGeneratedSatCnf
        (orderFortyNineH9ProfileMasks orderFortyNineH9T2Systems[0]!)) := by
  native_decide

end Erdos85
