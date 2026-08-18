import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t2_rep1`.
    source_cnf_sha256=12498caa61c8a62fcb94eac04213eda2e71eda60975598458ad37737b9ae671d
    compact_lrat_sha256=bd51dbd8512594031389ffbd4e8d9c2e4374e1ecc9b741b31cff510647614f06
    packed_lz4_sha256=1b18beb62b69eea0dc72a9bd262c91a7179ffdb7841a1ac7dd061ad09c6f865d
    packed_lz4_bytes=282701109
    lrat_actions=3155801 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT2Rep1ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t2_rep1.packed.lz4p7"

private def sevenHighT2Rep1Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT2Rep1ProofText
    247363470 462858990

theorem sevenHighT2Rep1Proof_size : sevenHighT2Rep1Proof.size = 3155801 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT2Rep1_check :
    LRAT.check sevenHighT2Rep1Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 2 1)) := by
  native_decide

theorem sevenHighT2Rep1_excluded :
    SevenHighCanonicalRepresentativeExcluded 2 1 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    2 1 sevenHighT2Rep1Proof sevenHighT2Rep1_check

end Erdos85
