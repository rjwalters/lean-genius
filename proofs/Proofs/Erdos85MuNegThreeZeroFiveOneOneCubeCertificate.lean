import Proofs.Erdos85MuNegThreeZeroFiveOneOneCubeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked corrected h305 one/one-shore cube certificates -/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegThreeZeroFiveCorrectOneOneS0OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s0_opp00.compact.lrat")
  else if missing.val = 1 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s0_opp01.compact.lrat")
  else if missing.val = 2 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s0_opp02.compact.lrat")
  else parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s0_opp03.compact.lrat")

def muNegThreeZeroFiveCorrectOneOneS1OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s1_opp00.compact.lrat")
  else if missing.val = 1 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s1_opp01.compact.lrat")
  else if missing.val = 2 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s1_opp02.compact.lrat")
  else parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_oneone_s1_opp03.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectOneOneS0Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectOneOneS0OppProof missing)
      (muNegThreeZeroFiveCorrectOneOneS0OppCubeCnf missing) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectOneOneS1Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectOneOneS1OppProof missing)
      (muNegThreeZeroFiveCorrectOneOneS1OppCubeCnf missing) := by
  native_decide

theorem muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectOneOneS0OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectOneOneS0Opp_check missing)

theorem muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectOneOneS1OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectOneOneS1Opp_check missing)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat
#print axioms Erdos85.muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat

