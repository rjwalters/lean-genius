import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1425
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=559 profileIndexed=true rawInventoryTable=true
    orbit=eea59a47105c38ec
    compact_lrat_sha256=1d27a1d62dd55657550dc96488b41a47c9e4661d61cdfd8f3b3c5c302faac111
    raw_lrat_sha256=361050aadae6346df542fc9e86c6d80f5e5ef9038746491c284e6d205ecef99c
    cnf_sha256=a35c501324a94c7e1d706a0b174d31b98588c33374f7ed03848d9c93e57e7ffe
    binary_lrat_sha256=366807b522a8d650fae00b105cad43d9093765b273d1c4c1eb04b8c64bb2ae6e
    lz4_frame_sha256=9530f88e29be90c613b1410753a360b7871a4561c9517efb13db5bfe80fed03f
    packed_lz4_sha256=5747fdfed0fcffec7fe38e29a5a750aa897a43adb548062ef944d10a4956fb19
    compact_bytes=1494375927 binary_bytes=658510743
    lz4_frame_bytes=388337369 packed_lz4_bytes=443814136
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01425Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1425, by native_decide⟩

private def h1V2P0I01425ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/57/5747fdfed0fcffec7fe38e29a5a750aa897a43adb548062ef944d10a4956fb19.lrat.lz4p7"

private def h1V2P0I01425RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01425ProofText
    388337369 658510743

private def h1V2P0I01425Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01425Table)
    h1V2P0I01425RawProof).toOption.get!

private theorem h1V2P0I01425Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01425Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01425Table).clauses.toList.all
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
private theorem h1V2P0I01425Check :
    LRAT.check h1V2P0I01425Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01425Table)
        h1V2P0I01425RawProof) := by
  native_decide

theorem h1V2P0I01425Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01425Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01425Nonzero
    h1V2P0I01425RawProof h1V2P0I01425Proof h1V2P0I01425Check

def h1V2P0I01425Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01425Table
  checked := h1V2P0I01425Checked

end Erdos85
