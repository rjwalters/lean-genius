import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase
namespace Erdos85
open Std Sat Std.Tactic.BVDecide
def localH3CoverProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof (include_str "proof.lrat")
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem localH3Cover_check : LRAT.check localH3CoverProof (orderFortyNineSmallHighLeftCoverCnf (orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf) (orderFortyNineThreeHighCubeLeftVariables orderFortyNineThreeHighDistOneNoCoincidenceMasks)) := by
  native_decide
theorem localH3Cover_unsat : (orderFortyNineSmallHighLeftCoverCnf (orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf) (orderFortyNineThreeHighCubeLeftVariables orderFortyNineThreeHighDistOneNoCoincidenceMasks)).Unsat :=
  LRAT.check_sound _ _ localH3Cover_check
#print axioms localH3Cover_unsat
end Erdos85
