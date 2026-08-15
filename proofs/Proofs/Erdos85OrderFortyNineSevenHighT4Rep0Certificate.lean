import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t4_rep0`.
    source_cnf_sha256=f14d3eb5faad3605ac8bdc5ec0b376edf0d7c56ea2000764b396c63cc770c17a
    compact_lrat_sha256=4621132a58efa73525f9f5a4660903405d37853b222fc119f0bc346a7a12e449
    packed_lz4_sha256=ee09ba97185ffbe66afb2a61289e49eefd6a679dd9a82c5e5d09641f332c2600
    packed_lz4_bytes=27847557
    lrat_actions=316062 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT4Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t4_rep0.packed.lz4p7"

private def sevenHighT4Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT4Rep0ProofText
    24366612 52020298

theorem sevenHighT4Rep0Proof_size : sevenHighT4Rep0Proof.size = 316062 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT4Rep0_check :
    LRAT.check sevenHighT4Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 4 0)) := by
  native_decide

theorem sevenHighT4Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 4 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    4 0 sevenHighT4Rep0Proof sevenHighT4Rep0_check

end Erdos85
