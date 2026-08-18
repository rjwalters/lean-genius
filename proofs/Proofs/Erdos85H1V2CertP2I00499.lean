import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=499
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=5
    orbit=1b9e3613b22439a4
    compact_lrat_sha256=46e22d57e9d1697add40a90c6e7411cd86a7f63909932c67a27ce94bb5cc221e
    raw_lrat_sha256=75b5c5a432342ababb1be0819a55626e8aa3a3c308152316772ce52c73880aa4
    cnf_sha256=774a16946f7566395f2c4bdf83549dc36a6bb6abecb80abe0533c8681d930131
    binary_lrat_sha256=fde3093809de0bf5c0555157ef72e119a62bd206ec6e7aa537542caaa05f7041
    lz4_frame_sha256=02ed28b99319460558bfac50ba60d36867fd73405633cd7571486fd92a66a4b6
    packed_lz4_sha256=6bb83db227e4ec53fb2db7169eb7df2057afe22e7e4c991430af2df8ebd10231
    compact_bytes=107085357 binary_bytes=46429816
    lz4_frame_bytes=28351338 packed_lz4_bytes=32401530
    source_cnf_clauses=610324 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00499Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨5, by native_decide⟩

private def h1V2P2I00499ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/6b/6bb83db227e4ec53fb2db7169eb7df2057afe22e7e4c991430af2df8ebd10231.lrat.lz4p7"

private def h1V2P2I00499RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00499ProofText
    28351338 46429816

private def h1V2P2I00499Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00499Table)
    h1V2P2I00499RawProof).toOption.get!

private theorem h1V2P2I00499Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00499Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00499Table).clauses.toList.all
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
private theorem h1V2P2I00499Check :
    LRAT.check h1V2P2I00499Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00499Table)
        h1V2P2I00499RawProof) := by
  native_decide

theorem h1V2P2I00499Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00499Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00499Nonzero
    h1V2P2I00499RawProof h1V2P2I00499Proof h1V2P2I00499Check

def h1V2P2I00499Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00499Table
  checked := h1V2P2I00499Checked

end Erdos85
