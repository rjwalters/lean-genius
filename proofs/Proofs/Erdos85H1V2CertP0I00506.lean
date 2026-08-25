import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=506
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=202 profileIndexed=true rawInventoryTable=true
    orbit=56a11a5d30775403
    compact_lrat_sha256=a120dd9a13ddca599c728192d84afb0d6d1eb33ea3f2c4c89ed468eb4235efac
    raw_lrat_sha256=b5586d5eeb09adb01323aa29b83de6b114f8d4cb395351d1849a51905cca9017
    cnf_sha256=553a8258b634228d8839c98b462b18117c07e011d74069dc69d00595fa1c8075
    binary_lrat_sha256=ac2c74860a8a506c69076cc951629c155e189fa29cf71584c87350d59706a46d
    lz4_frame_sha256=4367bfc882708eabf683b1bad57df6cc4f1ddeb050ebb07e9ad421f115b1abf6
    packed_lz4_sha256=8257dd157ad0567c0f23f8121f81b81d04dac154b7da987f413cabcd06b45c19
    compact_bytes=695573467 binary_bytes=306045029
    lz4_frame_bytes=184414802 packed_lz4_bytes=210759774
    source_cnf_clauses=613196 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00506Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨506, by native_decide⟩

private def h1V2P0I00506ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/82/8257dd157ad0567c0f23f8121f81b81d04dac154b7da987f413cabcd06b45c19.lrat.lz4p7"

private def h1V2P0I00506RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00506ProofText
    184414802 306045029

private def h1V2P0I00506Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00506Table)
    h1V2P0I00506RawProof).toOption.get!

private theorem h1V2P0I00506Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00506Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00506Table).clauses.toList.all
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
private theorem h1V2P0I00506Check :
    LRAT.check h1V2P0I00506Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00506Table)
        h1V2P0I00506RawProof) := by
  native_decide

theorem h1V2P0I00506Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00506Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00506Nonzero
    h1V2P0I00506RawProof h1V2P0I00506Proof h1V2P0I00506Check

def h1V2P0I00506Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00506Table
  checked := h1V2P0I00506Checked

end Erdos85
