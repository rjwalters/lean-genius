import Proofs.Erdos85MuNegThreeZeroFiveOwnerCubeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked corrected h305 zero/zero phase-zero cube certificates -/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegThreeZeroFiveCorrectZZS0OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s0_opp00.compact.lrat")
  else if missing.val = 1 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s0_opp01.compact.lrat")
  else if missing.val = 2 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s0_opp02.compact.lrat")
  else
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s0_opp03.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectZZS0Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectZZS0OppProof missing)
      (muNegThreeZeroFiveCorrectZZS0OppCubeCnf missing) := by
  native_decide

theorem muNegThreeZeroFiveCorrectZZS0OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectZZS0OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectZZS0Opp_check missing)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectZZS0OppCube_unsat
