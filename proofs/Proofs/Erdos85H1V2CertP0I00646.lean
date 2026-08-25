import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=646
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=257 profileIndexed=true rawInventoryTable=true
    orbit=6ea61c9e95a24521
    compact_lrat_sha256=b592b1938004d305aba0ddf1804f912def249dfdaa1c18a21b5bb3bdfd1c9641
    raw_lrat_sha256=75c1f8d5f080a81f0746fabff37c85718cbdeb07202832c2eb21e063d6b52f1c
    cnf_sha256=ac26eac9d42438387819daaff05b8764754a92c702edfa5c89769dfa106969a2
    binary_lrat_sha256=fd0df0168da47f8cf6f581640e6a24f609c063ea5154a6f91cb1001ddd287e91
    lz4_frame_sha256=eaf0e943195a9d3e54090cbec6a45b3a9f6d66d93b1ebad3c289e9807f7e4109
    packed_lz4_sha256=b119b1da06bc1e994ea3a3fd3fcfa73d016568c0907180b7e8375995ec24d735
    compact_bytes=2829294446 binary_bytes=1262211950
    lz4_frame_bytes=735321923 packed_lz4_bytes=840367912
    source_cnf_clauses=613180 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00646Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨646, by native_decide⟩

private def h1V2P0I00646ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b1/b119b1da06bc1e994ea3a3fd3fcfa73d016568c0907180b7e8375995ec24d735.lrat.lz4p7"

private def h1V2P0I00646RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00646ProofText
    735321923 1262211950

private def h1V2P0I00646Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00646Table)
    h1V2P0I00646RawProof).toOption.get!

private theorem h1V2P0I00646Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00646Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00646Table).clauses.toList.all
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
private theorem h1V2P0I00646Check :
    LRAT.check h1V2P0I00646Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00646Table)
        h1V2P0I00646RawProof) := by
  native_decide

theorem h1V2P0I00646Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00646Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00646Nonzero
    h1V2P0I00646RawProof h1V2P0I00646Proof h1V2P0I00646Check

def h1V2P0I00646Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00646Table
  checked := h1V2P0I00646Checked

end Erdos85
