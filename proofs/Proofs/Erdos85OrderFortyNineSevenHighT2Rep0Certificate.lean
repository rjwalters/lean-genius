import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t2_rep0`.
    source_cnf_sha256=c70e7d20d07705107748b92c85820ff7a6a9e2832028103917459c7357dc6b6d
    compact_lrat_sha256=b44a6853e08b0fbf4dfde1bbd4175d9acbbe85267c2599f2583fbd356466486d
    packed_lz4_sha256=67fac24bf5d3235056a52bec78d79a341b25735425173996f20d4a01d2819aa6
    packed_lz4_bytes=242814350
    lrat_actions=2636658 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT2Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t2_rep0.packed.lz4p7"

private def sevenHighT2Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT2Rep0ProofText
    212462556 397317230

theorem sevenHighT2Rep0Proof_size : sevenHighT2Rep0Proof.size = 2636658 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT2Rep0_check :
    LRAT.check sevenHighT2Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 2 0)) := by
  native_decide

theorem sevenHighT2Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 2 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    2 0 sevenHighT2Rep0Proof sevenHighT2Rep0_check

end Erdos85
