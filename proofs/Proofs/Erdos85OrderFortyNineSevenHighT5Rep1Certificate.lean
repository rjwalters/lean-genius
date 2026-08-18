import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t5_rep1`.
    source_cnf_sha256=999d879a94dced8f45efcd31ffea4cd0987e8fc3876f4fcc77807ce3b0ae5a31
    compact_lrat_sha256=a21ca44d023365351dcb96c2bedba73f3193aba12285600ecf25fe628a6aa652
    packed_lz4_sha256=2071ec2e30bb36b9a9323928ba66eef22895833778f55aa2b5497eca292cf613
    packed_lz4_bytes=74253
    lrat_actions=1979 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT5Rep1ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t5_rep1.packed.lz4p7"

private def sevenHighT5Rep1Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT5Rep1ProofText
    64971 124464

theorem sevenHighT5Rep1Proof_size : sevenHighT5Rep1Proof.size = 1979 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT5Rep1_check :
    LRAT.check sevenHighT5Rep1Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 5 1)) := by
  native_decide

theorem sevenHighT5Rep1_excluded :
    SevenHighCanonicalRepresentativeExcluded 5 1 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    5 1 sevenHighT5Rep1Proof sevenHighT5Rep1_check

end Erdos85
