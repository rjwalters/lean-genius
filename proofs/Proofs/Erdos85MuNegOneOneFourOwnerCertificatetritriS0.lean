import Proofs.Erdos85MuNegOneOneFourOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! One independently compiled LRAT terminal for the μ=-1 (1,4)
owner-grid case `tritri` with sign phase σ=0 (kissat `--plain`,
drat-trim pure-RUP, lrat-check verified, compacted). -/

namespace Erdos85

open Std.Tactic.BVDecide

def muNegOneOneFourtritriS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg1_onefour_tritri_s0.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegOneOneFourOwner_check_tritri_s0 :
    LRAT.check muNegOneOneFourtritriS0Proof
      (muNegOneOneFourOwnerSatCnf true true false) := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegOneOneFourOwner_check_tritri_s0
