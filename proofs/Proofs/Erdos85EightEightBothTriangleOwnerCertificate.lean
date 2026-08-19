import Proofs.Erdos85EightEightBothTriangleOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the both-all-triangle eight-plus-eight owner system

The source CNF has 648 variables and 89,584 clauses.  Kissat, with
extension-producing preprocessing disabled, produced a pure-RUP DRAT proof;
`drat-trim` independently verified and converted it to compact LRAT.

Source CNF SHA-256:
`6a1e3d54426f768329774d84a98aff8df1fca6d29d1d854fd94002cfa1938df1`.

Compact LRAT SHA-256:
`b8f71e0475bbb103b231bfe20f4c0dd6260417fdcbe1bbb067415bd970e4650d`.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def eightEightBothTriangleOwnerProofText : String :=
  include_str "Certificates" / "eight_eight_both_triangle_owner.compact.lrat"

def eightEightBothTriangleOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof eightEightBothTriangleOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightBothTriangleOwnerProof_size :
    eightEightBothTriangleOwnerProof.size = 2431 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightBothTriangleOwner_check :
    LRAT.check eightEightBothTriangleOwnerProof eightEightBothTriangleOwnerSatCnf := by
  native_decide

end Erdos85
