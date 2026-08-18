import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t4_rep1`.
    source_cnf_sha256=5bbd6a69f22e6ba5093fa8ec431f5ffb5c23b972f4a98d729aa4a7adb730a82c
    compact_lrat_sha256=f976b8f319741d0bd291239f9c5e045edebf8cdce63cb2cc8538c00e07bee7b9
    packed_lz4_sha256=7b8f91902bbd99b262905dc6f6c0cb81326e63dee160fb9fa8b68050bcbdcb8a
    packed_lz4_bytes=111808266
    lrat_actions=1007709 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT4Rep1ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t4_rep1.packed.lz4p7"

private def sevenHighT4Rep1Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT4Rep1ProofText
    97832232 211484983

theorem sevenHighT4Rep1Proof_size : sevenHighT4Rep1Proof.size = 1007709 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT4Rep1_check :
    LRAT.check sevenHighT4Rep1Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 4 1)) := by
  native_decide

theorem sevenHighT4Rep1_excluded :
    SevenHighCanonicalRepresentativeExcluded 4 1 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    4 1 sevenHighT4Rep1Proof sevenHighT4Rep1_check

end Erdos85
