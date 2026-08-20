import Proofs.Erdos85MuNegThreeZeroFiveOwnerCubeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked corrected h305 zero/zero phase-one cube certificates -/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegThreeZeroFiveCorrectZZS1OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s1_opp00.compact.lrat")
  else if missing.val = 1 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s1_opp01.compact.lrat")
  else if missing.val = 2 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s1_opp02.compact.lrat")
  else
    parseOrderFortyNineLratProof
      (include_str "Certificates" /
        "muneg3_zerofive_correct_zz_s1_opp03.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectZZS1Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectZZS1OppProof missing)
      (muNegThreeZeroFiveCorrectZZS1OppCubeCnf missing) := by
  native_decide

theorem muNegThreeZeroFiveCorrectZZS1OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectZZS1OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectZZS1Opp_check missing)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectZZS1OppCube_unsat
