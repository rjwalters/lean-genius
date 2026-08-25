import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=191
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=88 profileIndexed=true rawInventoryTable=true
    orbit=1d573a89e87f42e3
    compact_lrat_sha256=d0f40057d9a5cc5acf6b0d821a548a5f0bd8b630f0b1832664c4ab09f50a5284
    raw_lrat_sha256=b3ab09e89bd3a14049f91c9447154fa6511776ff37c376a8dee8706bc5675aec
    cnf_sha256=31a36cbc1baa36c4912d67fe2ad0fa52a9634d48db56e09ea4869922de36cc60
    binary_lrat_sha256=0109667f26aae279a11754bb9cc344f25ece637ca139647fd4f1e9ba119eded3
    lz4_frame_sha256=456889d00266f73a46081b64f557240533d8c8d3d27b96eab8cb23f3102b7edb
    packed_lz4_sha256=60bf9cafa4d98ddfbd3d92a6075e9544925ce25af7dd66303b6f3c8c30362afc
    compact_bytes=1650116158 binary_bytes=738497536
    lz4_frame_bytes=415956554 packed_lz4_bytes=475378919
    source_cnf_clauses=613196 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00191Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨191, by native_decide⟩

private def h1V2P0I00191ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/60/60bf9cafa4d98ddfbd3d92a6075e9544925ce25af7dd66303b6f3c8c30362afc.lrat.lz4p7"

private def h1V2P0I00191RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00191ProofText
    415956554 738497536

private def h1V2P0I00191Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00191Table)
    h1V2P0I00191RawProof).toOption.get!

private theorem h1V2P0I00191Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00191Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00191Table).clauses.toList.all
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
private theorem h1V2P0I00191Check :
    LRAT.check h1V2P0I00191Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00191Table)
        h1V2P0I00191RawProof) := by
  native_decide

theorem h1V2P0I00191Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00191Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00191Nonzero
    h1V2P0I00191RawProof h1V2P0I00191Proof h1V2P0I00191Check

def h1V2P0I00191Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00191Table
  checked := h1V2P0I00191Checked

end Erdos85
