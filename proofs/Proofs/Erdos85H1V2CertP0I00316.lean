import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=316
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=133 profileIndexed=true rawInventoryTable=true
    orbit=3406c0bd7fbb83ab
    compact_lrat_sha256=b491cd0f30ec283ad6d8e00a182987efa9941896a4fb2cfa558e83e294f46980
    raw_lrat_sha256=fa17a982a10214989cac478fe46b736c9b361d0ef38aa67e06144f680886c383
    cnf_sha256=0f9afd1bc1f1e66b2e34f71d333dd8981d33399c65f365296dfcc8d5f51e25b0
    binary_lrat_sha256=c32ed9be368222687b22fc0abff8a832d245e48d91751733589b9e2a1f22a88c
    lz4_frame_sha256=c68c8ed9dc88fd1720265404f91e4291e488deeffdb020fc600f59aeaa49b7d8
    packed_lz4_sha256=5809896408546d8756fca0028e617a3eb7628a4526f615a5983091db90d75643
    compact_bytes=1975879534 binary_bytes=880472498
    lz4_frame_bytes=514238414 packed_lz4_bytes=587701045
    source_cnf_clauses=613068 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00316Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨316, by native_decide⟩

private def h1V2P0I00316ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/58/5809896408546d8756fca0028e617a3eb7628a4526f615a5983091db90d75643.lrat.lz4p7"

private def h1V2P0I00316RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00316ProofText
    514238414 880472498

private def h1V2P0I00316Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00316Table)
    h1V2P0I00316RawProof).toOption.get!

private theorem h1V2P0I00316Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00316Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00316Table).clauses.toList.all
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
private theorem h1V2P0I00316Check :
    LRAT.check h1V2P0I00316Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00316Table)
        h1V2P0I00316RawProof) := by
  native_decide

theorem h1V2P0I00316Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00316Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00316Nonzero
    h1V2P0I00316RawProof h1V2P0I00316Proof h1V2P0I00316Check

def h1V2P0I00316Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00316Table
  checked := h1V2P0I00316Checked

end Erdos85
