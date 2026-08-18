import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t5_rep0`.
    source_cnf_sha256=c79b3293d51914c5ee06a609f011903322467db5bfc06da1b26bacf5a35e65c1
    compact_lrat_sha256=e6150ffd1d82276fc65fe3b6074123244a651e1ddcff54ad5987b6905e366341
    packed_lz4_sha256=9d269eb2716c8d10bc75b16f2d1df69c3e21348e2a7d21ec6d78575dc40f9950
    packed_lz4_bytes=14069
    lrat_actions=347 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT5Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t5_rep0.packed.lz4p7"

private def sevenHighT5Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT5Rep0ProofText
    12310 25977

theorem sevenHighT5Rep0Proof_size : sevenHighT5Rep0Proof.size = 347 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT5Rep0_check :
    LRAT.check sevenHighT5Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 5 0)) := by
  native_decide

theorem sevenHighT5Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 5 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    5 0 sevenHighT5Rep0Proof sevenHighT5Rep0_check

end Erdos85
