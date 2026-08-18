import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t3_rep2`.
    source_cnf_sha256=06d60da77f9bc80d6e32367e0cebafbb024a7c7f4bd97bb0ad0d43862122dabb
    compact_lrat_sha256=58e68a43d52600a30a31ffe8bfb40139ce52ec10af5c9d7efcc5822b23eb4eef
    packed_lz4_sha256=dc1a15c7f5e632c50fbf31a70fc2f77f8e8b7b0c312e2341ee3c9b8a02138b62
    packed_lz4_bytes=151252856
    lrat_actions=1619671 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT3Rep2ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t3_rep2.packed.lz4p7"

private def sevenHighT3Rep2Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT3Rep2ProofText
    132346249 251382944

theorem sevenHighT3Rep2Proof_size : sevenHighT3Rep2Proof.size = 1619671 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT3Rep2_check :
    LRAT.check sevenHighT3Rep2Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 3 2)) := by
  native_decide

theorem sevenHighT3Rep2_excluded :
    SevenHighCanonicalRepresentativeExcluded 3 2 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    3 2 sevenHighT3Rep2Proof sevenHighT3Rep2_check

end Erdos85
