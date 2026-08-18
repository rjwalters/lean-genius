import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t1_rep0`.
    source_cnf_sha256=6699c73daa88c3911597cf54251627584c6f0f32474ba6c52cff460d36778b9a
    compact_lrat_sha256=e83341791f8da4b173e28797e1522fe3977882bccec58b4d40c987db83f5ae47
    packed_lz4_sha256=9dd64dc3ab530f1b5c94b9ecdc7ab01eda9c0079349673f610643a459510fed6
    packed_lz4_bytes=1606429555
    lrat_actions=14332419 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT1Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t1_rep0.packed.lz4p7"

private def sevenHighT1Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT1Rep0ProofText
    1405625860 2680553030

theorem sevenHighT1Rep0Proof_size : sevenHighT1Rep0Proof.size = 14332419 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT1Rep0_check :
    LRAT.check sevenHighT1Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 1 0)) := by
  native_decide

theorem sevenHighT1Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 1 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    1 0 sevenHighT1Rep0Proof sevenHighT1Rep0_check

end Erdos85
