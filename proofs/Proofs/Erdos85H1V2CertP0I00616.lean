import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=616
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=244 profileIndexed=true rawInventoryTable=true
    orbit=6a0f08fc0ef15328
    compact_lrat_sha256=da354685b7e4e24e6b05fa8143f2ae1fa12f60e28a7212f56f4de66b91b72271
    raw_lrat_sha256=974744dcfc54257f9495534edb20cbd1652195ca6c25ff75750d24879b7ec9a7
    cnf_sha256=f85724aa98b54acd4e4f8af87c0ea1779aa727c65f29cccb2babb93eed2a7dcb
    binary_lrat_sha256=d07c8044c28df27a84dd12c56fe065d64025e94d99b5afd9058ac9b5232b24bd
    lz4_frame_sha256=515d59c45f9304531620f2f2449311899b2fd3e5e634d7b41c2bc725aad2a09c
    packed_lz4_sha256=b33eb31d1979faa890918383aaecba7bc6806342efd07f61105c7e46070590a0
    compact_bytes=988673956 binary_bytes=439174218
    lz4_frame_bytes=260555231 packed_lz4_bytes=297777407
    source_cnf_clauses=613156 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00616Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨616, by native_decide⟩

private def h1V2P0I00616ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b3/b33eb31d1979faa890918383aaecba7bc6806342efd07f61105c7e46070590a0.lrat.lz4p7"

private def h1V2P0I00616RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00616ProofText
    260555231 439174218

private def h1V2P0I00616Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00616Table)
    h1V2P0I00616RawProof).toOption.get!

private theorem h1V2P0I00616Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00616Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00616Table).clauses.toList.all
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
private theorem h1V2P0I00616Check :
    LRAT.check h1V2P0I00616Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00616Table)
        h1V2P0I00616RawProof) := by
  native_decide

theorem h1V2P0I00616Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00616Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00616Nonzero
    h1V2P0I00616RawProof h1V2P0I00616Proof h1V2P0I00616Check

def h1V2P0I00616Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00616Table
  checked := h1V2P0I00616Checked

end Erdos85
