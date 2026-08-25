import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=522
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=206 profileIndexed=true rawInventoryTable=true
    orbit=59ce2cc349119099
    compact_lrat_sha256=7c2b859bcf361ef056365e21083b352e44a3ed5bd7f6e3f3ef3ed770e1eba639
    raw_lrat_sha256=c1f345a4f80e5f4f0660c66c2736ce087d788c938b8efc355f7cb3a6e10dfd63
    cnf_sha256=0ff750bd77efd7831e2e6556318c361e7f33cdd48a3694d19260c3a013e97f22
    binary_lrat_sha256=f6603eddaf8c94f74660468cd13e2dff22c31b60dd654229a6aa6759e4e1f112
    lz4_frame_sha256=caae8cc1dc3985a3faf0890669fc8f28be19770cc7c0431b3c31ad6310e27635
    packed_lz4_sha256=cbf206aec236e771650e016bdca697a129a56e6eb3f2678fea7baffe15ec18b3
    compact_bytes=704724255 binary_bytes=311794722
    lz4_frame_bytes=178099779 packed_lz4_bytes=203542605
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00522Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨522, by native_decide⟩

private def h1V2P0I00522ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/cb/cbf206aec236e771650e016bdca697a129a56e6eb3f2678fea7baffe15ec18b3.lrat.lz4p7"

private def h1V2P0I00522RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00522ProofText
    178099779 311794722

private def h1V2P0I00522Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00522Table)
    h1V2P0I00522RawProof).toOption.get!

private theorem h1V2P0I00522Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00522Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00522Table).clauses.toList.all
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
private theorem h1V2P0I00522Check :
    LRAT.check h1V2P0I00522Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00522Table)
        h1V2P0I00522RawProof) := by
  native_decide

theorem h1V2P0I00522Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00522Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00522Nonzero
    h1V2P0I00522RawProof h1V2P0I00522Proof h1V2P0I00522Check

def h1V2P0I00522Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00522Table
  checked := h1V2P0I00522Checked

end Erdos85
