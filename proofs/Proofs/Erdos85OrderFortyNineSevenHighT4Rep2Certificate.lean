import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t4_rep2`.
    source_cnf_sha256=9fa93084d09800cda1e4d6e44570f6f0126f82b323da9e3c28bd305dce64601a
    compact_lrat_sha256=ac2be635cae79928038eca0601d893c33111abae2cb0147976fb95838cd674bf
    packed_lz4_sha256=d1d83e4b6eb06e9bb0c6dac00e220cf160eb50dd9f4f6d4825935775dee3cfca
    packed_lz4_bytes=57330516
    lrat_actions=592362 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT4Rep2ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t4_rep2.packed.lz4p7"

private def sevenHighT4Rep2Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT4Rep2ProofText
    50164201 109230134

theorem sevenHighT4Rep2Proof_size : sevenHighT4Rep2Proof.size = 592362 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT4Rep2_check :
    LRAT.check sevenHighT4Rep2Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 4 2)) := by
  native_decide

theorem sevenHighT4Rep2_excluded :
    SevenHighCanonicalRepresentativeExcluded 4 2 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    4 2 sevenHighT4Rep2Proof sevenHighT4Rep2_check

end Erdos85
