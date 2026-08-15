import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! GENERATED checked packed LRAT certificate for `h7_t6_rep0`.
    source_cnf_sha256=16825dda98f4945fadd04c2e30428dd2df832be5432d78e82e7d06264c9a8470
    compact_lrat_sha256=a5bf51a2268f318511d140e9fc7634cb534554022a62ec49e31aa9219c012fd2
    packed_lz4_sha256=20f31d094c4363112f057cdcdf1ec041aad97c364fbe6df704dc191ecc98e6e1
    packed_lz4_bytes=10770
    lrat_actions=285 -/

namespace Erdos85

open Std.Tactic.BVDecide

private def sevenHighT6Rep0ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t6_rep0.packed.lz4p7"

private def sevenHighT6Rep0Proof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof sevenHighT6Rep0ProofText
    9423 19325

theorem sevenHighT6Rep0Proof_size : sevenHighT6Rep0Proof.size = 285 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem sevenHighT6Rep0_check :
    LRAT.check sevenHighT6Rep0Proof
      (orderFortyNineGeneratedH7SatCnf
        (OrderFortyNineSevenHighCensus.representativeMasks 6 0)) := by
  native_decide

theorem sevenHighT6Rep0_excluded :
    SevenHighCanonicalRepresentativeExcluded 6 0 :=
  sevenHighCanonicalRepresentativeExcluded_of_lrat
    6 0 sevenHighT6Rep0Proof sevenHighT6Rep0_check

end Erdos85
