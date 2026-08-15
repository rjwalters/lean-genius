import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t3_rep1`.
    source_cnf_sha256=ccf36d58acb43047488c0206d10261751569fbd2c3bd85a65d7f8593a1b5c890
    compact_lrat_sha256=21c2bc9e54e27f205652ee74052042b8b5d62a8ae0598a5ab145ed0b5259d888
    packed_lz4_sha256=5e489cbbb5b2cedd57fe5d66d285cd257fdff4d694e2338db2a2c2e889efa004
    packed_lz4_bytes=59150879
    lrat_actions=665095 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT3Rep1ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t3_rep1.packed.lz4p7"

private def sevenHighT3Rep1Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT3Rep1ProofText
    51757019 97870038

theorem sevenHighT3Rep1Proof_size : sevenHighT3Rep1Proof.size = 665095 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT3Rep1_check :
    LRAT.check sevenHighT3Rep1Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 3 1)) := by
  native_decide

theorem sevenHighT3Rep1_excluded :
    SevenHighCanonicalRepresentativeExcluded 3 1 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    3 1 sevenHighT3Rep1Proof sevenHighT3Rep1_check

end Erdos85
