import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=511
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=203 profileIndexed=true rawInventoryTable=true
    orbit=579a19b4b3d03c21
    compact_lrat_sha256=4c140b43a93dc22dd184eca03868dbbb5b9ab90532995c0f205cdeb18c110d98
    raw_lrat_sha256=340a4b9ea25c8b064ce5d2d06e4f37ecb932880d1f8ba448c9e5730764f18622
    cnf_sha256=05511a81a0b7447806971e7829adf82305a133568673a14e8f73d901555c8d01
    binary_lrat_sha256=cdef775c87c52e335bcc5dec494d269d630b5186d0c6a41712bdef594f3828ea
    lz4_frame_sha256=2677f2b5e218d49577b46ae5a075ade2fe3a0729b557da5b34c4b06d0b99e67b
    packed_lz4_sha256=512c86f1100373e0ef0b5f443c3756695e046d645358e26b8165214667f83ba7
    compact_bytes=1729385223 binary_bytes=766506051
    lz4_frame_bytes=446344889 packed_lz4_bytes=510108445
    source_cnf_clauses=613260 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00511Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨511, by native_decide⟩

private def h1V2P0I00511ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/51/512c86f1100373e0ef0b5f443c3756695e046d645358e26b8165214667f83ba7.lrat.lz4p7"

private def h1V2P0I00511RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00511ProofText
    446344889 766506051

private def h1V2P0I00511Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00511Table)
    h1V2P0I00511RawProof).toOption.get!

private theorem h1V2P0I00511Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00511Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00511Table).clauses.toList.all
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
private theorem h1V2P0I00511Check :
    LRAT.check h1V2P0I00511Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00511Table)
        h1V2P0I00511RawProof) := by
  native_decide

theorem h1V2P0I00511Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00511Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00511Nonzero
    h1V2P0I00511RawProof h1V2P0I00511Proof h1V2P0I00511Check

def h1V2P0I00511Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00511Table
  checked := h1V2P0I00511Checked

end Erdos85
