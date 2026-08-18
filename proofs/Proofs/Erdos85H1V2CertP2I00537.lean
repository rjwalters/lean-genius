import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=537
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=8
    orbit=1db3058f29cc49d5
    compact_lrat_sha256=faf03e081707d548c3baaa2d511f9920205276dfa95af79e0bcd916a6f70b555
    raw_lrat_sha256=f6a4d2b14c17bd0a96d0e11689073139f89b064c7e7b3922cc5e934030ee127c
    cnf_sha256=d45bf6358a997bb9fe1813f998a951c8066f6b2182a52f6951983213f2b5d760
    binary_lrat_sha256=4d5785e81ded1c4e62196aa4a5c2bc233820adbd8814354f97dae6efe8b8226e
    lz4_frame_sha256=f0c235bbc94ae2925abedc54f49e822cee7f4df0685df8e9038e739278b9a4be
    packed_lz4_sha256=4a0ad9f0eed055c57d09190282f6b6436c48aff40033189e8b719df4e407dad8
    compact_bytes=2514702250 binary_bytes=1140985071
    lz4_frame_bytes=678922137 packed_lz4_bytes=775911014
    source_cnf_clauses=610424 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00537Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨8, by native_decide⟩

private def h1V2P2I00537ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/4a/4a0ad9f0eed055c57d09190282f6b6436c48aff40033189e8b719df4e407dad8.lrat.lz4p7"

private def h1V2P2I00537RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00537ProofText
    678922137 1140985071

private def h1V2P2I00537Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00537Table)
    h1V2P2I00537RawProof).toOption.get!

private theorem h1V2P2I00537Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00537Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00537Table).clauses.toList.all
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
private theorem h1V2P2I00537Check :
    LRAT.check h1V2P2I00537Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00537Table)
        h1V2P2I00537RawProof) := by
  native_decide

theorem h1V2P2I00537Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00537Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00537Nonzero
    h1V2P2I00537RawProof h1V2P2I00537Proof h1V2P2I00537Check

def h1V2P2I00537Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00537Table
  checked := h1V2P2I00537Checked

end Erdos85
