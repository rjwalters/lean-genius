import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=299
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=126 profileIndexed=true rawInventoryTable=true
    orbit=319f0e376d24bdf7
    compact_lrat_sha256=bca6e1abeebb9eda77a548c1e55444be09bf1c1eef9c247fcb27e0770a4081de
    raw_lrat_sha256=ac326005a9835dcfc9799cb4d428d7ad95e2687b730244e41a5888cb289305e8
    cnf_sha256=863dd0dfe5eee7620be3c34195c3ee10761e561087b77a9e42f4221f7c3651e8
    binary_lrat_sha256=9346f896fc88b18c56a9c75025df6f6873606e597036e2fa0bc3be093fd3d6f5
    lz4_frame_sha256=99f0ae2b86728c79f0f7105b5a637ddce0166fcdd45e74866ea238bb1cf2cf59
    packed_lz4_sha256=968ade1dec787f80215602022ea1972a3ec75dd488ed174251f5a2203c395f42
    compact_bytes=960516343 binary_bytes=426139802
    lz4_frame_bytes=251606983 packed_lz4_bytes=287550838
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00299Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨299, by native_decide⟩

private def h1V2P0I00299ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/96/968ade1dec787f80215602022ea1972a3ec75dd488ed174251f5a2203c395f42.lrat.lz4p7"

private def h1V2P0I00299RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00299ProofText
    251606983 426139802

private def h1V2P0I00299Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00299Table)
    h1V2P0I00299RawProof).toOption.get!

private theorem h1V2P0I00299Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00299Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00299Table).clauses.toList.all
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
private theorem h1V2P0I00299Check :
    LRAT.check h1V2P0I00299Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00299Table)
        h1V2P0I00299RawProof) := by
  native_decide

theorem h1V2P0I00299Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00299Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00299Nonzero
    h1V2P0I00299RawProof h1V2P0I00299Proof h1V2P0I00299Check

def h1V2P0I00299Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00299Table
  checked := h1V2P0I00299Checked

end Erdos85
