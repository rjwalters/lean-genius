import Proofs.Erdos85MuNegThreeZeroFiveOwnerCubeCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked h305 zero/zero phase-one row-cube certificates -/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegThreeZeroFiveZZS1OppProof (missing : Fin 4) : Array LRAT.IntAction :=
  if missing.val = 0 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" / "muneg3_zerofive_zz_s1_opp0.compact.lrat")
  else if missing.val = 1 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" / "muneg3_zerofive_zz_s1_opp1.compact.lrat")
  else if missing.val = 2 then
    parseOrderFortyNineLratProof
      (include_str "Certificates" / "muneg3_zerofive_zz_s1_opp2.compact.lrat")
  else
    parseOrderFortyNineLratProof
      (include_str "Certificates" / "muneg3_zerofive_zz_s1_opp3.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegThreeZeroFiveZZS1Opp_check : ∀ missing : Fin 4,
    LRAT.check (muNegThreeZeroFiveZZS1OppProof missing)
      (muNegThreeZeroFiveZZS1OppCubeCnf missing) := by
  native_decide

theorem muNegThreeZeroFiveZZS1OppCube_unsat (missing : Fin 4) :
    (muNegThreeZeroFiveZZS1OppCubeCnf missing).Unsat := by
  exact LRAT.check_sound _ _ (muNegThreeZeroFiveZZS1Opp_check missing)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveZZS1OppCube_unsat
