import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1400
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=549 profileIndexed=true rawInventoryTable=true
    orbit=eb4b0f334d1663be
    compact_lrat_sha256=95ecd60e1845351bc2cd89c33a71e41efb62be1b92210e3c76e8f0d328fecae8
    raw_lrat_sha256=2e2e64e2f440548c72774b794931b5181776e918a62bea36741d9ec298b4f0ae
    cnf_sha256=7cb28d03f0f563a019cd2a6ccbfa96975448d8546264e2aabc80e104b9c24c70
    binary_lrat_sha256=ad9973b320a134ae477875362367cabae55e5941abddc21a582db78aff7de048
    lz4_frame_sha256=dbface3850e22bbd24e99d773b3e75ed8cb6cadf3924e3dc422d2fe05f22bbb9
    packed_lz4_sha256=be5574a0422b34887db5d2e706cb2a45b13c0d431eb640f7bdb731f2a0a8ccb7
    compact_bytes=2215043097 binary_bytes=977969555
    lz4_frame_bytes=587006386 packed_lz4_bytes=670864442
    source_cnf_clauses=613156 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01400Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1400, by native_decide⟩

private def h1V2P0I01400ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/be/be5574a0422b34887db5d2e706cb2a45b13c0d431eb640f7bdb731f2a0a8ccb7.lrat.lz4p7"

private def h1V2P0I01400RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01400ProofText
    587006386 977969555

private def h1V2P0I01400Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01400Table)
    h1V2P0I01400RawProof).toOption.get!

private theorem h1V2P0I01400Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01400Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01400Table).clauses.toList.all
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
private theorem h1V2P0I01400Check :
    LRAT.check h1V2P0I01400Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01400Table)
        h1V2P0I01400RawProof) := by
  native_decide

theorem h1V2P0I01400Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01400Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01400Nonzero
    h1V2P0I01400RawProof h1V2P0I01400Proof h1V2P0I01400Check

def h1V2P0I01400Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01400Table
  checked := h1V2P0I01400Checked

end Erdos85
