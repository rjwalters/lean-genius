import Proofs.Erdos85EightEightLowOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the low eight-plus-eight owner system

The source CNF has 640 variables and 86,384 clauses.  Kissat, with
extension-producing preprocessing disabled, produced a short DRAT proof;
`drat-trim` independently verified and converted it to a pure-RUP compact
LRAT proof, and `lrat-check` also returned VERIFIED.

Source CNF SHA-256:
`429a7d2f32628619b400eee0aed5b01fcf73b335ef1a7036db602c30d52de70c`.

Compact LRAT SHA-256:
`a1f7fc1e0179155391c0964dff65da3d7e18c88e1d52d5a7f26833bbafa220cf`.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def eightEightLowOwnerProofText : String :=
  include_str "Certificates" / "eight_eight_low_owner.compact.lrat"

def eightEightLowOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof eightEightLowOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightLowOwnerProof_size :
    eightEightLowOwnerProof.size = 3282 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightLowOwner_check :
    LRAT.check eightEightLowOwnerProof eightEightLowOwnerSatCnf := by
  native_decide

end Erdos85
