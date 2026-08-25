import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=940
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=374 profileIndexed=true rawInventoryTable=true
    orbit=9e2e97a76667d75f
    compact_lrat_sha256=485330a44596c9adb898c4fe94a731109afbca5c979b0936f509d003c380b55b
    raw_lrat_sha256=18f50549d8278492848fb3d3c43b4cb96b1854384ec608fc0e2ae331c8074ddd
    cnf_sha256=d5323da600e376e029f714a8ca8c25033cd1c81a99aff2535d6ef9400b46b09d
    binary_lrat_sha256=8842d8f09bc0ed7198ae608f360b75de0aaa296daf6c7f5644c25d4b4feff0dd
    lz4_frame_sha256=cefebec18cbd2f93511800da4232abd440d02fd9145a11abbfc7dcd959631287
    packed_lz4_sha256=98edc54417886d0c68872e12a8811ac871ceb0cc194ba99c62b0ebbe9c6eedbd
    compact_bytes=1238592867 binary_bytes=544936140
    lz4_frame_bytes=319646814 packed_lz4_bytes=365310645
    source_cnf_clauses=613032 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00940Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨940, by native_decide⟩

private def h1V2P0I00940ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/98/98edc54417886d0c68872e12a8811ac871ceb0cc194ba99c62b0ebbe9c6eedbd.lrat.lz4p7"

private def h1V2P0I00940RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00940ProofText
    319646814 544936140

private def h1V2P0I00940Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00940Table)
    h1V2P0I00940RawProof).toOption.get!

private theorem h1V2P0I00940Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00940Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00940Table).clauses.toList.all
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
private theorem h1V2P0I00940Check :
    LRAT.check h1V2P0I00940Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00940Table)
        h1V2P0I00940RawProof) := by
  native_decide

theorem h1V2P0I00940Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00940Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00940Nonzero
    h1V2P0I00940RawProof h1V2P0I00940Proof h1V2P0I00940Check

def h1V2P0I00940Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00940Table
  checked := h1V2P0I00940Checked

end Erdos85
