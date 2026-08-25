import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=739
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=295 profileIndexed=true rawInventoryTable=true
    orbit=7ce6b96f5a1beb9d
    compact_lrat_sha256=df4fbcec822063f46f49b6075bafcb214e8b2a81a0967e9ba5a9c78fc48fce61
    raw_lrat_sha256=69a1136347d91ae306b8c1820b5c7115f216ffec90aa64dae38f132f7b869b80
    cnf_sha256=343f9fc94113a03d7c749a5a17042b8b56241775ee8175ac07a528897028fd64
    binary_lrat_sha256=26e6ec2df24230160837032e0588c25a2f6ff7173505bc63b58a3d73931c6111
    lz4_frame_sha256=a35630700ae3740464957b0186ab785e674cf6a9046174007a6869cb22b4442a
    packed_lz4_sha256=241aaae198a90e2d95a7c0f785c1564f24b59c782ef8e56357fd1984da563f5c
    compact_bytes=2481267139 binary_bytes=1096489457
    lz4_frame_bytes=644885996 packed_lz4_bytes=737012567
    source_cnf_clauses=613160 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00739Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨739, by native_decide⟩

private def h1V2P0I00739ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/24/241aaae198a90e2d95a7c0f785c1564f24b59c782ef8e56357fd1984da563f5c.lrat.lz4p7"

private def h1V2P0I00739RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00739ProofText
    644885996 1096489457

private def h1V2P0I00739Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00739Table)
    h1V2P0I00739RawProof).toOption.get!

private theorem h1V2P0I00739Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00739Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00739Table).clauses.toList.all
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
private theorem h1V2P0I00739Check :
    LRAT.check h1V2P0I00739Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00739Table)
        h1V2P0I00739RawProof) := by
  native_decide

theorem h1V2P0I00739Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00739Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00739Nonzero
    h1V2P0I00739RawProof h1V2P0I00739Proof h1V2P0I00739Check

def h1V2P0I00739Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00739Table
  checked := h1V2P0I00739Checked

end Erdos85
