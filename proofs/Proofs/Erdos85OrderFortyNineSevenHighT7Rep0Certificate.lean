import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t7_rep0`.
    source_cnf_sha256=a2a409bc957ffe391805a4df1154a6f0a8ef091f1a888bc870effb63a6ffa1f2
    compact_lrat_sha256=3d9940e3581ce9463e615657293846044cd54d47561d49ec9a58e06c3a4d8a5d
    packed_lz4_sha256=51ea373567837d90fde4b8b3145afab9220c4d0ca3b240d51ccda8a4929edab2
    packed_lz4_bytes=5982
    lrat_actions=163 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT7Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t7_rep0.packed.lz4p7"

private def sevenHighT7Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT7Rep0ProofText
    5234 10102

theorem sevenHighT7Rep0Proof_size : sevenHighT7Rep0Proof.size = 163 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT7Rep0_check :
    LRAT.check sevenHighT7Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 7 0)) := by
  native_decide

theorem sevenHighT7Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 7 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    7 0 sevenHighT7Rep0Proof sevenHighT7Rep0_check

end Erdos85
