import Proofs.Erdos85SixTenMixedOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked LRAT terminal for the mixed six-plus-ten owner system

The source CNF has 640 variables and 86,186 clauses.  Kissat, with
extension-producing preprocessing disabled, produced a pure-RUP DRAT proof;
`drat-trim` independently verified and converted it to compact LRAT.

Source CNF SHA-256:
`44b8d262fb98e2e38973e2c0db89d31d9ed54b72e7dee5e52367df0821576c7c`.

Compact LRAT SHA-256:
`b06fd06defaa4ae87a387075683f283711e203b195b97d7d268f349bed54d259`.
-/

namespace Erdos85

open Std.Tactic.BVDecide

def sixTenMixedOwnerProofText : String :=
  include_str "Certificates" / "six_ten_mixed_owner.compact.lrat"

def sixTenMixedOwnerProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof sixTenMixedOwnerProofText

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sixTenMixedOwnerProof_size :
    sixTenMixedOwnerProof.size = 3312 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sixTenMixedOwner_check :
    LRAT.check sixTenMixedOwnerProof sixTenMixedOwnerSatCnf := by
  native_decide

end Erdos85
