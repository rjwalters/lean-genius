import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=138
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=66 profileIndexed=true rawInventoryTable=true
    orbit=15323c66ee731e64
    compact_lrat_sha256=ae6f4dd8af3465ca363d0a8c1a36ebb5047ba82d2e810fbc4022f4c89600b8b0
    raw_lrat_sha256=1824be9eb0f191a23eb503906a0434b886560de8179489a8d00fd5ebaaca7a3e
    cnf_sha256=3ec57137580767ab960cec2873147772d0afaaefd718541a033bf5faa791d943
    binary_lrat_sha256=cde23329e2e745aa68279b7a25f597c93aeb7abbb497c436fcc9ac8c0c50e633
    lz4_frame_sha256=01bb2c2b9ac695d42204eea897b05c9eaf857f703261a0e6209d2d2497e47244
    packed_lz4_sha256=e2ff4de7db159322123f38e92630e4cc0f5b7278526d860086146066373c21ee
    compact_bytes=243494973 binary_bytes=105954367
    lz4_frame_bytes=59583258 packed_lz4_bytes=68095152
    source_cnf_clauses=613072 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00138Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨138, by native_decide⟩

private def h1V2P0I00138ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e2/e2ff4de7db159322123f38e92630e4cc0f5b7278526d860086146066373c21ee.lrat.lz4p7"

private def h1V2P0I00138RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00138ProofText
    59583258 105954367

private def h1V2P0I00138Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00138Table)
    h1V2P0I00138RawProof).toOption.get!

private theorem h1V2P0I00138Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00138Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00138Table).clauses.toList.all
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
private theorem h1V2P0I00138Check :
    LRAT.check h1V2P0I00138Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00138Table)
        h1V2P0I00138RawProof) := by
  native_decide

theorem h1V2P0I00138Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00138Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00138Nonzero
    h1V2P0I00138RawProof h1V2P0I00138Proof h1V2P0I00138Check

def h1V2P0I00138Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00138Table
  checked := h1V2P0I00138Checked

end Erdos85
