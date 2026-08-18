import Proofs.Erdos85LratRuntime
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked per-cell D-system certificate for all-triangle C10+C6

The DIMACS instance contains the all-triangle C10+C6 hole two-factor and the
exact row/column per-cell D-count laws in the single-fiber specialization.
The unique color is tautological, so the model has only hole and symmetric
diagonal-pair variables.  Its LRAT proof was independently checked by the
reference `lrat-check` implementation before being imported here.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

private def allTriangleTenSixPerCellCnfText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-percell-d/cnf/alltri_c10c6_fiber6.cnf"

/-- Deterministically generated all-triangle C10+C6 per-cell D-system. -/
def allTriangleTenSixPerCellCnf : CNF Nat :=
  match DimacsRuntime.parse allTriangleTenSixPerCellCnfText.toUTF8 with
  | .ok cnf => cnf
  | .error _ => { clauses := #[] }

private def allTriangleTenSixPerCellProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-order64-percell-d/lrat/alltri_c10c6_fiber6.lrat"

private def allTriangleTenSixPerCellRawProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof allTriangleTenSixPerCellProofText

private def allTriangleTenSixPerCellProof : Array LRAT.IntAction :=
  (prepareLratProof allTriangleTenSixPerCellCnf
    allTriangleTenSixPerCellRawProof).toOption.get!

def allTriangleTenSixPerCellPaddedCnf : CNF Nat :=
  LratExtensionVariables.padCnfForProof allTriangleTenSixPerCellCnf
    allTriangleTenSixPerCellRawProof

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem allTriangleTenSixPerCellCheck :
    LRAT.check allTriangleTenSixPerCellProof
      allTriangleTenSixPerCellPaddedCnf := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Trusted-checker conclusion: no all-triangle C10+C6 one-fiber per-cell
D-system exists.  The checker pads only for logically inert LRAT extension
variables. -/
theorem allTriangleTenSixPerCellPaddedCnf_unsat :
    allTriangleTenSixPerCellPaddedCnf.Unsat :=
  LRAT.check_sound allTriangleTenSixPerCellProof
    allTriangleTenSixPerCellPaddedCnf allTriangleTenSixPerCellCheck

end Erdos85

#print axioms Erdos85.allTriangleTenSixPerCellPaddedCnf_unsat
