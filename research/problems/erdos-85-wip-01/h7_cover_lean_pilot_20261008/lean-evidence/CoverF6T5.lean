import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat
import Proofs.Erdos85OrderFortyNineLratCertificateBase

namespace Erdos85.HsbCoverPilot.F6T5
open Std Sat Std.Tactic.BVDecide

def leafRows := SevenHighT0Hsb.leaves 3
  (sevenHighT0CanonicalEmptyRepresentativeMask 6 5)

def coverCnf : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 6 5 ++
    cnfOfClauseList (leafRows.map SevenHighT0Hsb.clause)

private def proofText : String := include_str "/workspace/research/problems/erdos-85-wip-01/h7_cover_lean_pilot_20261008/_build/cover-first/proof.lrat7"
private def rawProof : Array LRAT.IntAction :=
  parsePackedOrderFortyNineLratProof proofText 9870017
private def preparedProof : Array LRAT.IntAction :=
  match prepareLratProof coverCnf rawProof with
  | .ok proof => proof
  | .error _ => #[]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem check : LRAT.check preparedProof
    (LratExtensionVariables.padCnfForProof coverCnf rawProof) := by
  native_decide

theorem checkedCover : SevenHighT0CanonicalHsbCoverChecked 3 6 5 leafRows := by
  apply SevenHighT0CanonicalHsbCoverLratChecked.unsat
  exact ⟨rawProof, preparedProof, check⟩

end Erdos85.HsbCoverPilot.F6T5
#print axioms Erdos85.HsbCoverPilot.F6T5.check
#print axioms Erdos85.HsbCoverPilot.F6T5.checkedCover
