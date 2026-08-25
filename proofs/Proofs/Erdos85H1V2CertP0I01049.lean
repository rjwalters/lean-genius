import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1049
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=412 profileIndexed=true rawInventoryTable=true
    orbit=b1aa470cb10a0f4a
    compact_lrat_sha256=8a6a642aae290db11561b693f7ae38765169077afae8f7c6d4bd433bc99d7c87
    raw_lrat_sha256=632e6db7e504afed89f6393d7edb2213a200f67e62b0d74561bb29553bf1e67d
    cnf_sha256=5595a73e0d63d057942a61cfa1256bd61d47715566722a12c5bd97fea6c82e93
    binary_lrat_sha256=709a59c8ecb36e1e65bea9bdb3041d1cb7d969c0283e046ba98a0e0c22f76baf
    lz4_frame_sha256=54f1049652258e44fef400485707a3480543ea3e3e76230e7a1158c03e93fce4
    packed_lz4_sha256=8f3ae51dc327008bbcd72c714468dd168fccb06ddb765973c60dff0a7766fb41
    compact_bytes=1219572459 binary_bytes=540114879
    lz4_frame_bytes=320403944 packed_lz4_bytes=366175936
    source_cnf_clauses=612972 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01049Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1049, by native_decide⟩

private def h1V2P0I01049ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/8f/8f3ae51dc327008bbcd72c714468dd168fccb06ddb765973c60dff0a7766fb41.lrat.lz4p7"

private def h1V2P0I01049RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01049ProofText
    320403944 540114879

private def h1V2P0I01049Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01049Table)
    h1V2P0I01049RawProof).toOption.get!

private theorem h1V2P0I01049Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01049Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01049Table).clauses.toList.all
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
private theorem h1V2P0I01049Check :
    LRAT.check h1V2P0I01049Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01049Table)
        h1V2P0I01049RawProof) := by
  native_decide

theorem h1V2P0I01049Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01049Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01049Nonzero
    h1V2P0I01049RawProof h1V2P0I01049Proof h1V2P0I01049Check

def h1V2P0I01049Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01049Table
  checked := h1V2P0I01049Checked

end Erdos85
