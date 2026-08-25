import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1485
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=587 profileIndexed=true rawInventoryTable=true
    orbit=f7da138edf386e74
    compact_lrat_sha256=8221552a3cd2289d9d2f909ba5368e042335ae4e899866352ccb9fca7190a1b3
    raw_lrat_sha256=990fbb5e37c587f71feb8f9da2a4c784792a7d352ed531c9978240872a84b1d5
    cnf_sha256=23234664238e8dca7649462a6bb4d7065cb3ba13cc5303f3f8e9cf37062a3223
    binary_lrat_sha256=586086b48561795f2d9a88635b7bd8bf504dc55245ffeea34ad2da3e8a3f3646
    lz4_frame_sha256=562a11470fb337ffc832831c1faa020a4dcdca0c179665e37a506bba9b9e09b1
    packed_lz4_sha256=bb4b40e487ea3851fab92ddd9a14d9efa6a49e545fe71977d38154b25ca6b9a7
    compact_bytes=444166264 binary_bytes=194468151
    lz4_frame_bytes=110998110 packed_lz4_bytes=126854983
    source_cnf_clauses=613062 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01485Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1485, by native_decide⟩

private def h1V2P0I01485ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bb/bb4b40e487ea3851fab92ddd9a14d9efa6a49e545fe71977d38154b25ca6b9a7.lrat.lz4p7"

private def h1V2P0I01485RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01485ProofText
    110998110 194468151

private def h1V2P0I01485Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01485Table)
    h1V2P0I01485RawProof).toOption.get!

private theorem h1V2P0I01485Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01485Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01485Table).clauses.toList.all
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
private theorem h1V2P0I01485Check :
    LRAT.check h1V2P0I01485Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01485Table)
        h1V2P0I01485RawProof) := by
  native_decide

theorem h1V2P0I01485Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01485Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01485Nonzero
    h1V2P0I01485RawProof h1V2P0I01485Proof h1V2P0I01485Check

def h1V2P0I01485Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01485Table
  checked := h1V2P0I01485Checked

end Erdos85
