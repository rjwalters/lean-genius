import Proofs.Erdos85SixTenAllTfOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the both-all-TF 6+10 owner system

The source CNF has 640 variables and 86,606 clauses.  Kissat with
`--plain` (no extension-producing preprocessing) produced a pure-RUP
DRAT proof; `drat-trim` independently verified and converted it to LRAT
(1783 of 2031 lemmas in core, 66,143 resolution steps, 0 RAT lemmas),
and `lrat-check` also returned VERIFIED.

Source CNF SHA-256:
`c5d9b90b259a6c0b3f610318e66edb28b4c4abf181324181e082b139127b848b`.

Embedded compact LRAT SHA-256 (raw drat-trim LRAT
`68a92b…a828f` compacted to consecutive derived identifiers):
`ecd7b934e2fa6dfcaebb81dab46700b687f57b7177cc3b5e7e9c0d1cff0ce4ec`.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def sixTenAllTfOwnerProofText : String :=
  include_str "Certificates" / "six_ten_alltf_owner.compact.lrat"

def sixTenAllTfOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof sixTenAllTfOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sixTenAllTfOwnerProof_size :
    sixTenAllTfOwnerProof.size = 3106 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sixTenAllTfOwner_check :
    LRAT.check sixTenAllTfOwnerProof sixTenAllTfOwnerSatCnf := by
  native_decide

end Erdos85
