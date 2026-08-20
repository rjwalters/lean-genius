import Proofs.Erdos85MuNegThreeZeroFiveMixedCubeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked corrected h305 mixed-shore cube certificates -/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegThreeZeroFiveCorrectMixedS0OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s0_opp00.compact.lrat")
  else if missing.val = 1 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s0_opp01.compact.lrat")
  else if missing.val = 2 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s0_opp02.compact.lrat")
  else parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s0_opp03.compact.lrat")

def muNegThreeZeroFiveCorrectMixedS1OppProof (missing : Fin 4) :
    Array LRAT.IntAction :=
  if missing.val = 0 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s1_opp00.compact.lrat")
  else if missing.val = 1 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s1_opp01.compact.lrat")
  else if missing.val = 2 then parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s1_opp02.compact.lrat")
  else parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_correct_mixed_s1_opp03.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectMixedS0Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectMixedS0OppProof missing)
      (muNegThreeZeroFiveCorrectMixedS0OppCubeCnf missing) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveCorrectMixedS1Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveCorrectMixedS1OppProof missing)
      (muNegThreeZeroFiveCorrectMixedS1OppCubeCnf missing) := by
  native_decide

theorem muNegThreeZeroFiveCorrectMixedS0OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectMixedS0OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectMixedS0Opp_check missing)

theorem muNegThreeZeroFiveCorrectMixedS1OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveCorrectMixedS1OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _
    (muNegThreeZeroFiveCorrectMixedS1Opp_check missing)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectMixedS0OppCube_unsat
#print axioms Erdos85.muNegThreeZeroFiveCorrectMixedS1OppCube_unsat
