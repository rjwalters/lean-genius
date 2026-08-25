import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=297
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=124 profileIndexed=true rawInventoryTable=true
    orbit=3151303b651a1de5
    compact_lrat_sha256=fd973341d83622064c83a2e27dd0ec6360a71d9b50bdbcda0154be548011daf7
    raw_lrat_sha256=6ffdd37a5acffb93fb777ca2a4d56720738a47c2bee52382428a700d2db743d0
    cnf_sha256=97b80a7af0276e087c4705151ce1009952e7fbdb2162e9ba809d6c9d3a4c4a90
    binary_lrat_sha256=bfc5573c8a63c7db22ef1876c705adf9ebd98598462f13e74dd46000f5bcdec6
    lz4_frame_sha256=acd949bbd4a7576bfb5da13fedca041f917113d0f37ff837f44355c9b32d9569
    packed_lz4_sha256=969ef389a005e1a4b4a43f5f03b5a507c9dfbc3cb9d2f8099c1f519d0ad56930
    compact_bytes=571645757 binary_bytes=250465547
    lz4_frame_bytes=150873371 packed_lz4_bytes=172426710
    source_cnf_clauses=613004 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00297Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨297, by native_decide⟩

private def h1V2P0I00297ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/96/969ef389a005e1a4b4a43f5f03b5a507c9dfbc3cb9d2f8099c1f519d0ad56930.lrat.lz4p7"

private def h1V2P0I00297RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00297ProofText
    150873371 250465547

private def h1V2P0I00297Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00297Table)
    h1V2P0I00297RawProof).toOption.get!

private theorem h1V2P0I00297Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00297Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00297Table).clauses.toList.all
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
private theorem h1V2P0I00297Check :
    LRAT.check h1V2P0I00297Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00297Table)
        h1V2P0I00297RawProof) := by
  native_decide

theorem h1V2P0I00297Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00297Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00297Nonzero
    h1V2P0I00297RawProof h1V2P0I00297Proof h1V2P0I00297Check

def h1V2P0I00297Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00297Table
  checked := h1V2P0I00297Checked

end Erdos85
