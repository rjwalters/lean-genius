import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=583
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=225 profileIndexed=true rawInventoryTable=true
    orbit=62f05b12cac57fa8
    compact_lrat_sha256=7529733378f74cb5aa658a61509136b7757939a3852c74476d74479b147d223a
    raw_lrat_sha256=50e59911045e3b4c92b00ca84efeac8ab0b5fe37417229e09e261a0d2efe8f28
    cnf_sha256=dec653cc103c65995130e904f86a85693fe58bf6af9aa9aea806eb90ba9fc627
    binary_lrat_sha256=2dd88fb8d5452b20463dfc2a7c7ff3e2757cf8639f17e0574456bf8590942266
    lz4_frame_sha256=c2e6166345984bdd474573b1283de50e07f9afa513f1002318ec7d2bb5c01c30
    packed_lz4_sha256=3050cf99af7313e333530d8a884e5495421f6d75ba5dff070dd52ccf63c25652
    compact_bytes=838511913 binary_bytes=368597760
    lz4_frame_bytes=222519572 packed_lz4_bytes=254308083
    source_cnf_clauses=613208 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00583Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨583, by native_decide⟩

private def h1V2P0I00583ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/30/3050cf99af7313e333530d8a884e5495421f6d75ba5dff070dd52ccf63c25652.lrat.lz4p7"

private def h1V2P0I00583RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00583ProofText
    222519572 368597760

private def h1V2P0I00583Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00583Table)
    h1V2P0I00583RawProof).toOption.get!

private theorem h1V2P0I00583Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00583Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00583Table).clauses.toList.all
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
private theorem h1V2P0I00583Check :
    LRAT.check h1V2P0I00583Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00583Table)
        h1V2P0I00583RawProof) := by
  native_decide

theorem h1V2P0I00583Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00583Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00583Nonzero
    h1V2P0I00583RawProof h1V2P0I00583Proof h1V2P0I00583Check

def h1V2P0I00583Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00583Table
  checked := h1V2P0I00583Checked

end Erdos85
