import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1479
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=584 profileIndexed=true rawInventoryTable=true
    orbit=f6bf9e168f583f3a
    compact_lrat_sha256=2e02a55ae5c5515307f5880096d020ee6c7276895cbbec9c2931bc774d8f8163
    raw_lrat_sha256=435d1d26c7c1024397d924e84844054083ed878fcab36ca648b6c7a6bec8de7f
    cnf_sha256=cf4820246a357a43bf02685fbe5dfa0bf2648526ad5b8030cfbad9158cf4389e
    binary_lrat_sha256=1951b01f64afdd499b6918ec8f73e517c99916c63c17a40939bf03101ae0cbc6
    lz4_frame_sha256=abeb614259e928a34cb94f2a59e0f7e0480b1d9c86e2befbb6eb8aed3281818f
    packed_lz4_sha256=b9a111e37d7d9184f1dee5657282c25db4b76420c128e9b6919de5d7845f36b4
    compact_bytes=2419401749 binary_bytes=1075973518
    lz4_frame_bytes=609862028 packed_lz4_bytes=696985175
    source_cnf_clauses=613196 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01479Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1479, by native_decide⟩

private def h1V2P0I01479ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b9/b9a111e37d7d9184f1dee5657282c25db4b76420c128e9b6919de5d7845f36b4.lrat.lz4p7"

private def h1V2P0I01479RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01479ProofText
    609862028 1075973518

private def h1V2P0I01479Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01479Table)
    h1V2P0I01479RawProof).toOption.get!

private theorem h1V2P0I01479Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01479Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01479Table).clauses.toList.all
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
private theorem h1V2P0I01479Check :
    LRAT.check h1V2P0I01479Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01479Table)
        h1V2P0I01479RawProof) := by
  native_decide

theorem h1V2P0I01479Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01479Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01479Nonzero
    h1V2P0I01479RawProof h1V2P0I01479Proof h1V2P0I01479Check

def h1V2P0I01479Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01479Table
  checked := h1V2P0I01479Checked

end Erdos85
