import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1495
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=594 profileIndexed=true rawInventoryTable=true
    orbit=f941d236ef297d1d
    compact_lrat_sha256=d0d7793adafc39556997e6de2b51c2d785dd18a10597f4bd0cb05a5c1dd05dbd
    raw_lrat_sha256=48eaf905a1f2e48c5a66483978fd43507e38f8156ed9ac51ba8bce3c9f6f18b7
    cnf_sha256=dfd7486f0cf690427c9e37363c48b01101aeea439f25c255b78a912b0368c0c3
    binary_lrat_sha256=510fe28b06c995959e51aaf43b555e8ccc9d977af4729ec61e7a29c853002504
    lz4_frame_sha256=dccee2129b5a5e0fb071c35a45079977b3a0628f70a434e71eb1e82e1a823e4a
    packed_lz4_sha256=364ef87f7dbadfc23d19d84ce28ebcc1526ffffcfff38adcb7c08368c6b26d71
    compact_bytes=549646121 binary_bytes=241374848
    lz4_frame_bytes=141619479 packed_lz4_bytes=161850834
    source_cnf_clauses=613070 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01495Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1495, by native_decide⟩

private def h1V2P0I01495ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/36/364ef87f7dbadfc23d19d84ce28ebcc1526ffffcfff38adcb7c08368c6b26d71.lrat.lz4p7"

private def h1V2P0I01495RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01495ProofText
    141619479 241374848

private def h1V2P0I01495Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01495Table)
    h1V2P0I01495RawProof).toOption.get!

private theorem h1V2P0I01495Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01495Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01495Table).clauses.toList.all
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
private theorem h1V2P0I01495Check :
    LRAT.check h1V2P0I01495Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01495Table)
        h1V2P0I01495RawProof) := by
  native_decide

theorem h1V2P0I01495Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01495Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01495Nonzero
    h1V2P0I01495RawProof h1V2P0I01495Proof h1V2P0I01495Check

def h1V2P0I01495Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01495Table
  checked := h1V2P0I01495Checked

end Erdos85
