import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked certificates for the honest 88-owner h305 CNFs

The six computational checks use the repository's established
`native_decide` LRAT pipeline.  Consequently the exported unsatisfiability
theorems disclose `Lean.ofReduceBool` in addition to the ordinary logical
axioms, exactly like the existing owner-certificate modules.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def h305Owner88TfTfS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tf_tf_s0.lrat")

def h305Owner88TfTfS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tf_tf_s1.lrat")

def h305Owner88TfTriS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tf_tri_s0.lrat")

def h305Owner88TfTriS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tf_tri_s1.lrat")

def h305Owner88TriTriS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tri_tri_s0.lrat")

def h305Owner88TriTriS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg3_zerofive_honest_tri_tri_s1.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TfTfS0_check :
    LRAT.check h305Owner88TfTfS0Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf false false false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TfTfS1_check :
    LRAT.check h305Owner88TfTfS1Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf false false true) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TfTriS0_check :
    LRAT.check h305Owner88TfTriS0Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf false true false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TfTriS1_check :
    LRAT.check h305Owner88TfTriS1Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf false true true) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TriTriS0_check :
    LRAT.check h305Owner88TriTriS0Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf true true false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem h305Owner88TriTriS1_check :
    LRAT.check h305Owner88TriTriS1Proof
      (muNegThreeZeroFiveCorrectOwnerSatCnf true true true) := by
  native_decide

theorem h305Owner88TfTfS0_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf false false false).Unsat :=
  LRAT.check_sound _ _ h305Owner88TfTfS0_check

theorem h305Owner88TfTfS1_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf false false true).Unsat :=
  LRAT.check_sound _ _ h305Owner88TfTfS1_check

theorem h305Owner88TfTriS0_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf false true false).Unsat :=
  LRAT.check_sound _ _ h305Owner88TfTriS0_check

theorem h305Owner88TfTriS1_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf false true true).Unsat :=
  LRAT.check_sound _ _ h305Owner88TfTriS1_check

theorem h305Owner88TriTriS0_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf true true false).Unsat :=
  LRAT.check_sound _ _ h305Owner88TriTriS0_check

theorem h305Owner88TriTriS1_unsat :
    (muNegThreeZeroFiveCorrectOwnerSatCnf true true true).Unsat :=
  LRAT.check_sound _ _ h305Owner88TriTriS1_check

end Erdos85

#print axioms Erdos85.h305Owner88TfTfS0_unsat
#print axioms Erdos85.h305Owner88TfTfS1_unsat
#print axioms Erdos85.h305Owner88TfTriS0_unsat
#print axioms Erdos85.h305Owner88TfTriS1_unsat
#print axioms Erdos85.h305Owner88TriTriS0_unsat
#print axioms Erdos85.h305Owner88TriTriS1_unsat
