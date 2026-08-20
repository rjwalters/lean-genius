import Proofs.Erdos85MuNegOneOneFourOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! One independently compiled LRAT terminal for the μ=-1 (1,4)
owner-grid case `TFTF` with sign phase σ=1 (kissat `--plain`,
drat-trim pure-RUP, lrat-check verified, compacted). -/

namespace Erdos85

open Std.Tactic.BVDecide

def muNegOneOneFourTFTFS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg1_onefour_TFTF_s1.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegOneOneFourOwner_check_TFTF_s1 :
    LRAT.check muNegOneOneFourTFTFS1Proof
      (muNegOneOneFourOwnerSatCnf false false true) := by
  native_decide

end Erdos85

#print axioms Erdos85.muNegOneOneFourOwner_check_TFTF_s1
