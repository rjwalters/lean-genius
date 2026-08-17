import Proofs.Erdos85LratRuntime
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked finite certificates for the order-64 `[10,6]` branch -/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

private def tenSixRCompletenessCnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r_complete.cnf"

/-- The independently generated CNF asserting the full parity-strengthened
`R` ledger while excluding the six enumerated models. -/
def tenSixRCompletenessCnf : CNF Nat :=
  match DimacsRuntime.parse tenSixRCompletenessCnfText.toUTF8 with
  | .ok cnf => cnf
  | .error _ => { clauses := #[] }

private def tenSixRCompletenessProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r_complete.lrat"

private def tenSixRCompletenessRawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixRCompletenessProofText

private def tenSixRCompletenessProof : Array LRAT.IntAction :=
  (prepareLratProof tenSixRCompletenessCnf
    tenSixRCompletenessRawProof).toOption.get!

def tenSixRCompletenessPaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixRCompletenessCnf
    tenSixRCompletenessRawProof

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixRCompletenessCheck :
    LRAT.check tenSixRCompletenessProof tenSixRCompletenessPaddedCnf := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Trusted-checker conclusion: the `[10,6]` `R` ledger has no model beyond
the six explicitly excluded by the certificate CNF.  The checked CNF has one
logically inert tautology appended when the proof uses extension variables. -/
theorem tenSixRCompletenessPaddedCnf_unsat :
    tenSixRCompletenessPaddedCnf.Unsat :=
  LRAT.check_sound tenSixRCompletenessProof
    tenSixRCompletenessPaddedCnf tenSixRCompletenessCheck

private def tenSixC001CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r001.cnf"

def tenSixC001Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC001CnfText.toUTF8 with
  | .ok cnf => cnf
  | .error _ => { clauses := #[] }

private def tenSixC001ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r001.lrat"

private def tenSixC001RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC001ProofText

private def tenSixC001Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC001Cnf tenSixC001RawProof).toOption.get!

def tenSixC001PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC001Cnf tenSixC001RawProof

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC001Check :
    LRAT.check tenSixC001Proof tenSixC001PaddedCnf := by
  native_decide

/-- The first of the six possible `[10,6]` exterior-pair graphs admits no
C4-free outside block satisfying the exact cross-block service equations. -/
theorem tenSixC001PaddedCnf_unsat : tenSixC001PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC001Proof tenSixC001PaddedCnf tenSixC001Check

private def tenSixC002CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r002.cnf"
def tenSixC002Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC002CnfText.toUTF8 with
  | .ok cnf => cnf | .error _ => { clauses := #[] }
private def tenSixC002ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r002.lrat"
private def tenSixC002RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC002ProofText
private def tenSixC002Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC002Cnf tenSixC002RawProof).toOption.get!
def tenSixC002PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC002Cnf tenSixC002RawProof
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC002Check :
    LRAT.check tenSixC002Proof tenSixC002PaddedCnf := by native_decide
theorem tenSixC002PaddedCnf_unsat : tenSixC002PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC002Proof tenSixC002PaddedCnf tenSixC002Check

private def tenSixC003CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r003.cnf"
def tenSixC003Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC003CnfText.toUTF8 with
  | .ok cnf => cnf | .error _ => { clauses := #[] }
private def tenSixC003ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r003.lrat"
private def tenSixC003RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC003ProofText
private def tenSixC003Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC003Cnf tenSixC003RawProof).toOption.get!
def tenSixC003PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC003Cnf tenSixC003RawProof
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC003Check :
    LRAT.check tenSixC003Proof tenSixC003PaddedCnf := by native_decide
theorem tenSixC003PaddedCnf_unsat : tenSixC003PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC003Proof tenSixC003PaddedCnf tenSixC003Check

private def tenSixC004CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r004.cnf"
def tenSixC004Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC004CnfText.toUTF8 with
  | .ok cnf => cnf | .error _ => { clauses := #[] }
private def tenSixC004ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r004.lrat"
private def tenSixC004RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC004ProofText
private def tenSixC004Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC004Cnf tenSixC004RawProof).toOption.get!
def tenSixC004PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC004Cnf tenSixC004RawProof
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC004Check :
    LRAT.check tenSixC004Proof tenSixC004PaddedCnf := by native_decide
theorem tenSixC004PaddedCnf_unsat : tenSixC004PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC004Proof tenSixC004PaddedCnf tenSixC004Check

private def tenSixC005CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r005.cnf"
def tenSixC005Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC005CnfText.toUTF8 with
  | .ok cnf => cnf | .error _ => { clauses := #[] }
private def tenSixC005ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r005.lrat"
private def tenSixC005RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC005ProofText
private def tenSixC005Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC005Cnf tenSixC005RawProof).toOption.get!
def tenSixC005PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC005Cnf tenSixC005RawProof
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC005Check :
    LRAT.check tenSixC005Proof tenSixC005PaddedCnf := by native_decide
theorem tenSixC005PaddedCnf_unsat : tenSixC005PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC005Proof tenSixC005PaddedCnf tenSixC005Check

private def tenSixC006CnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/cnf/r006.cnf"
def tenSixC006Cnf : CNF Nat :=
  match DimacsRuntime.parse tenSixC006CnfText.toUTF8 with
  | .ok cnf => cnf | .error _ => { clauses := #[] }
private def tenSixC006ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-ten-six/lrat/r006.lrat"
private def tenSixC006RawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof tenSixC006ProofText
private def tenSixC006Proof : Array LRAT.IntAction :=
  (prepareLratProof tenSixC006Cnf tenSixC006RawProof).toOption.get!
def tenSixC006PaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof tenSixC006Cnf tenSixC006RawProof
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem tenSixC006Check :
    LRAT.check tenSixC006Proof tenSixC006PaddedCnf := by native_decide
theorem tenSixC006PaddedCnf_unsat : tenSixC006PaddedCnf.Unsat :=
  LRAT.check_sound tenSixC006Proof tenSixC006PaddedCnf tenSixC006Check

end Erdos85
