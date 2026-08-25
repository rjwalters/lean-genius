import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=603
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=236 profileIndexed=true rawInventoryTable=true
    orbit=66715cf9469e0f25
    compact_lrat_sha256=4957943de5eb1a7b54e866729c597f8ed1346deafb3f80a070ee56162c5fc91a
    raw_lrat_sha256=a9e77936417e1f3b12c0b42498cca8d0d845f9b2a4d80da7b0f14a7c861e1507
    cnf_sha256=bf58094470e13775aa8da91337e9ebd1dd011e6709531cf62d365088419864e3
    binary_lrat_sha256=4f5cfa7c696e0a240b4c1cddeddf7644cb34e83acfceb2d057910b227339cf9d
    lz4_frame_sha256=3b5b4b166e02448315932afc217798a9fae01b8fc7d199046a00afeb42be7c22
    packed_lz4_sha256=dd4b3cbe6a13ed3b73b43e470d59c1bcf0915354caa2d0d3601390b405e7e52b
    compact_bytes=1731659583 binary_bytes=767321262
    lz4_frame_bytes=451242616 packed_lz4_bytes=515705847
    source_cnf_clauses=613164 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00603Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨603, by native_decide⟩

private def h1V2P0I00603ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/dd/dd4b3cbe6a13ed3b73b43e470d59c1bcf0915354caa2d0d3601390b405e7e52b.lrat.lz4p7"

private def h1V2P0I00603RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00603ProofText
    451242616 767321262

private def h1V2P0I00603Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00603Table)
    h1V2P0I00603RawProof).toOption.get!

private theorem h1V2P0I00603Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00603Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00603Table).clauses.toList.all
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
private theorem h1V2P0I00603Check :
    LRAT.check h1V2P0I00603Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00603Table)
        h1V2P0I00603RawProof) := by
  native_decide

theorem h1V2P0I00603Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00603Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00603Nonzero
    h1V2P0I00603RawProof h1V2P0I00603Proof h1V2P0I00603Check

def h1V2P0I00603Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00603Table
  checked := h1V2P0I00603Checked

end Erdos85
