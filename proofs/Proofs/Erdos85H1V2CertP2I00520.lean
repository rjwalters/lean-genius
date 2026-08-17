import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=520
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=7
    orbit=1c94d915113952f8
    compact_lrat_sha256=23c7f4c6ba195bac90782f9b1e2ca31b19e5829fe26bc07a13ef706cb64ecbab
    raw_lrat_sha256=c6c0ff68c6c54389d83c62a5265d343892fd7536568b3dbac2c036c8e716b653
    cnf_sha256=06a74062afacafc049015192eb4e8084c82ce995df28f221c8cd271d66cfc7d2
    binary_lrat_sha256=716f99ab6e401b89bf3cd040cda842da736c5c67285ccde0e934989f658a3cb7
    lz4_frame_sha256=c5e41c91db91fc7a5e4bbd660aded3e26d5a12cee9c01d90ce9914d6dff7b5c4
    packed_lz4_sha256=98cd760651a7a64a9ce432f8ee4e263280f7150e6278388d35811b2654e025f2
    compact_bytes=5510254069 binary_bytes=2486705933
    lz4_frame_bytes=1502135026 packed_lz4_bytes=1716725744
    source_cnf_clauses=610476 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00520Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨7, by native_decide⟩

private def h1V2P2I00520ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/98/98cd760651a7a64a9ce432f8ee4e263280f7150e6278388d35811b2654e025f2.lrat.lz4p7"

private def h1V2P2I00520RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00520ProofText
    1502135026 2486705933

private def h1V2P2I00520Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00520Table)
    h1V2P2I00520RawProof).toOption.get!

private theorem h1V2P2I00520Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00520Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00520Table).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause
      (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem h1V2P2I00520Check :
    LRAT.check h1V2P2I00520Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00520Table)
        h1V2P2I00520RawProof) := by
  native_decide

theorem h1V2P2I00520Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00520Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00520Nonzero
    h1V2P2I00520RawProof h1V2P2I00520Proof h1V2P2I00520Check

def h1V2P2I00520Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00520Table
  checked := h1V2P2I00520Checked

end Erdos85
