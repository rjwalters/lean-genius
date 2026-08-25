import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=4 localIndex=680
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=239 profileIndexed=true rawInventoryTable=true
    orbit=d1526dbc33714c33
    compact_lrat_sha256=bd21cb83c3bf9ba4db30f5e9b768877ed9be826e9759bfe813ac38adb6e0ab78
    raw_lrat_sha256=84790c9119ca8ca2a03e56367cd2b1004c90d6c62bb3d39f84b321689b943be1
    cnf_sha256=1bae31b466f3332771ecbed67eb55cf4d3ca71174bcbd8a20e88f5c020f321dd
    binary_lrat_sha256=24d560fe835093b4344f64b34b58750f78cdcad9ad96b3ad7aac19d1745c021c
    lz4_frame_sha256=ceea1a552703432e01614e5fdfeac45e985272c7faadc00cce219a192a18033b
    packed_lz4_sha256=a085058b97b25bafa76af733637e73c21e7096e198e9adf66324953cdffded0c
    compact_bytes=1525646559 binary_bytes=673431390
    lz4_frame_bytes=341627809 packed_lz4_bytes=390431782
    source_cnf_clauses=607458 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P4I00680Table : OneHighMissTable :=
  (oneHighInventoryTables (4 : Fin 5)).get
    ⟨680, by native_decide⟩

private def h1V2P4I00680ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a0/a085058b97b25bafa76af733637e73c21e7096e198e9adf66324953cdffded0c.lrat.lz4p7"

private def h1V2P4I00680RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P4I00680ProofText
    341627809 673431390

private def h1V2P4I00680Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 4 h1V2P4I00680Table)
    h1V2P4I00680RawProof).toOption.get!

private theorem h1V2P4I00680Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 4 h1V2P4I00680Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 4 h1V2P4I00680Table).clauses.toList.all
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
private theorem h1V2P4I00680Check :
    LRAT.check h1V2P4I00680Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 4 h1V2P4I00680Table)
        h1V2P4I00680RawProof) := by
  native_decide

theorem h1V2P4I00680Checked :
    OneHighFamilyV2CheckedUnsat 4 h1V2P4I00680Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P4I00680Nonzero
    h1V2P4I00680RawProof h1V2P4I00680Proof h1V2P4I00680Check

def h1V2P4I00680Entry : OneHighFamilyV2CheckedEntry 4 where
  table := h1V2P4I00680Table
  checked := h1V2P4I00680Checked

end Erdos85
