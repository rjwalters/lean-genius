import Proofs.Erdos85EightEightMixedOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the mixed eight-plus-eight owner system

The source CNF has 644 variables and 87,952 clauses.  Kissat, with
extension-producing preprocessing disabled, produced a pure-RUP DRAT proof;
`drat-trim` independently verified and converted it to compact LRAT.

Source CNF SHA-256:
`3cb3ce12ef266a4c8132294c656f506b3f65012dfaf72def7aa4d964f4bed763`.

Compact LRAT SHA-256:
`2788ce1c32deed6920c219ef48bbbfaa4a599de477abde361940918562f88892`.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def eightEightMixedOwnerProofText : String :=
  include_str "Certificates" / "eight_eight_mixed_owner.compact.lrat"

def eightEightMixedOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof eightEightMixedOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightMixedOwnerProof_size :
    eightEightMixedOwnerProof.size = 4959 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem eightEightMixedOwner_check :
    LRAT.check eightEightMixedOwnerProof eightEightMixedOwnerSatCnf := by
  native_decide

end Erdos85
