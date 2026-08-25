import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=991
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=390 profileIndexed=true rawInventoryTable=true
    orbit=a77833c93e3405f8
    compact_lrat_sha256=c3c974bc513d06c982c500574d9e87f74bf2078020bd35e1d158ce35c23f398c
    raw_lrat_sha256=0c4fb7732f93325482cbc4434196cb86ffb6bb41a2ee63091b743bbff182e64c
    cnf_sha256=5a73ae6e0ba0b8fa5ba733e0d3c3ebb6be4e2f489a98829e71df8c264853ce3d
    binary_lrat_sha256=e78e4b4bb4ae7dae0eafc3c64af1a169f7dcde626985dde81e8c21a3e4b667df
    lz4_frame_sha256=a7b140ace541fbbee86d4f4e4a0c14f80b98708c3faed2c03ff73ac64ba2f9d3
    packed_lz4_sha256=83acd144442904051c294fa17bf14e2dc03d83b6990781280b1780e13d9c1547
    compact_bytes=608985393 binary_bytes=267173259
    lz4_frame_bytes=163467768 packed_lz4_bytes=186820307
    source_cnf_clauses=613224 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00991Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨991, by native_decide⟩

private def h1V2P0I00991ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/83/83acd144442904051c294fa17bf14e2dc03d83b6990781280b1780e13d9c1547.lrat.lz4p7"

private def h1V2P0I00991RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00991ProofText
    163467768 267173259

private def h1V2P0I00991Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00991Table)
    h1V2P0I00991RawProof).toOption.get!

private theorem h1V2P0I00991Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00991Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00991Table).clauses.toList.all
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
private theorem h1V2P0I00991Check :
    LRAT.check h1V2P0I00991Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00991Table)
        h1V2P0I00991RawProof) := by
  native_decide

theorem h1V2P0I00991Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00991Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00991Nonzero
    h1V2P0I00991RawProof h1V2P0I00991Proof h1V2P0I00991Check

def h1V2P0I00991Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00991Table
  checked := h1V2P0I00991Checked

end Erdos85
