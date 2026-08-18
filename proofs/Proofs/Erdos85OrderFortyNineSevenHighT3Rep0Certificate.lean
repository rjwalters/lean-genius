import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t3_rep0`.
    source_cnf_sha256=2f189eae275291b2fb217a3ab0c80421f105e86b396ac91c2b992b9536b2b7ec
    compact_lrat_sha256=b477ad2024cc9004cb455f8c54cad9d44b870939dbfe418d1d8be1fd7dc34061
    packed_lz4_sha256=3c8c60bc10e6c4eca551e1b754c681af0e16bc1f089522a254d938319d508bf3
    packed_lz4_bytes=35476195
    lrat_actions=435195 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT3Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t3_rep0.packed.lz4p7"

private def sevenHighT3Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT3Rep0ProofText
    31041670 58723974

theorem sevenHighT3Rep0Proof_size : sevenHighT3Rep0Proof.size = 435195 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT3Rep0_check :
    LRAT.check sevenHighT3Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 3 0)) := by
  native_decide

theorem sevenHighT3Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 3 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    3 0 sevenHighT3Rep0Proof sevenHighT3Rep0_check

end Erdos85
