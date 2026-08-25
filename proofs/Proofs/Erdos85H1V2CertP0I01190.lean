import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1190
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=471 profileIndexed=true rawInventoryTable=true
    orbit=c60116d55d32f668
    compact_lrat_sha256=cdbff675175d54f63b5f55cab7b2d361a5f9dc95c20b617531613eb7568d882c
    raw_lrat_sha256=a5d93095cf3770c5d15d4416d23a5a3d6b453551139e5687ffd6c41a81db7ec5
    cnf_sha256=fdf7fee3627974f9045d4a2bd08368afed65cb5048b5fe11373a6a31722c250f
    binary_lrat_sha256=0b957ceb969fe90b0964f3641f7701c1c79d5b0e5356fe82133248bcb66fb6ee
    lz4_frame_sha256=1e163c6d9d98d2eb136755f002fe3cb4fcb36e5860f41170ed51bdb8b6c40554
    packed_lz4_sha256=3ca7b442835eaf2a5cd55418aa0a66cb517e4d7a0c9c05fdbc3068f16d159ada
    compact_bytes=1031118227 binary_bytes=456517158
    lz4_frame_bytes=262956061 packed_lz4_bytes=300521213
    source_cnf_clauses=613164 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01190Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1190, by native_decide⟩

private def h1V2P0I01190ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/3c/3ca7b442835eaf2a5cd55418aa0a66cb517e4d7a0c9c05fdbc3068f16d159ada.lrat.lz4p7"

private def h1V2P0I01190RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01190ProofText
    262956061 456517158

private def h1V2P0I01190Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01190Table)
    h1V2P0I01190RawProof).toOption.get!

private theorem h1V2P0I01190Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01190Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01190Table).clauses.toList.all
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
private theorem h1V2P0I01190Check :
    LRAT.check h1V2P0I01190Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01190Table)
        h1V2P0I01190RawProof) := by
  native_decide

theorem h1V2P0I01190Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01190Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01190Nonzero
    h1V2P0I01190RawProof h1V2P0I01190Proof h1V2P0I01190Check

def h1V2P0I01190Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01190Table
  checked := h1V2P0I01190Checked

end Erdos85
