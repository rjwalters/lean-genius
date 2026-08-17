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

end Erdos85
