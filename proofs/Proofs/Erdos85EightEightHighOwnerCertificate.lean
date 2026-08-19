import Proofs.Erdos85EightEightHighOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the high eight-plus-eight owner system

The certificate refutes the variable-cross CNF, so it covers all twelve
labeled cross blocks satisfying the parity, degree, and intertwining
constraints rather than assuming a preselected circulant model.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def eightEightHighOwnerProofText : String :=
  include_str "Certificates" / "eight_eight_high_owner.compact.lrat"

def eightEightHighOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof eightEightHighOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightHighOwnerProof_size :
    eightEightHighOwnerProof.size = 40384 := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem eightEightHighOwner_check :
    LRAT.check eightEightHighOwnerProof eightEightHighOwnerSatCnf := by
  native_decide

end Erdos85
