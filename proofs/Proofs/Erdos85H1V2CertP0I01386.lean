import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1386
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=543 profileIndexed=true rawInventoryTable=true
    orbit=e8b2595fd103f042
    compact_lrat_sha256=dbddc8c4f421690cd9f773564909378bfcea1239f365388a4c0dbde647eb4eac
    raw_lrat_sha256=50d3ca3c2c88cf7aa849feda044108272d725addce2ad0a478366bad669a6d4a
    cnf_sha256=7562cf3a1963f86a8e6b11d064bd2327c8a97614589fa60b3bfe736f32fcbeae
    binary_lrat_sha256=eb4bc13d8c62f1cf538c18dc47c31b0fd4b01617ac7c6991b9c7ecdaca93d43a
    lz4_frame_sha256=7dd6ca47fdc1d6109f7771cf82ed2cf1c994a2250a597a81233e707237285ca0
    packed_lz4_sha256=090545816fc8d9264fbec1541bf0b52254188936abef4cf2d057260633fd816c
    compact_bytes=875491934 binary_bytes=386257948
    lz4_frame_bytes=224474615 packed_lz4_bytes=256542418
    source_cnf_clauses=613158 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01386Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1386, by native_decide⟩

private def h1V2P0I01386ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/09/090545816fc8d9264fbec1541bf0b52254188936abef4cf2d057260633fd816c.lrat.lz4p7"

private def h1V2P0I01386RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01386ProofText
    224474615 386257948

private def h1V2P0I01386Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01386Table)
    h1V2P0I01386RawProof).toOption.get!

private theorem h1V2P0I01386Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01386Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01386Table).clauses.toList.all
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
private theorem h1V2P0I01386Check :
    LRAT.check h1V2P0I01386Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01386Table)
        h1V2P0I01386RawProof) := by
  native_decide

theorem h1V2P0I01386Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01386Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01386Nonzero
    h1V2P0I01386RawProof h1V2P0I01386Proof h1V2P0I01386Check

def h1V2P0I01386Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01386Table
  checked := h1V2P0I01386Checked

end Erdos85
