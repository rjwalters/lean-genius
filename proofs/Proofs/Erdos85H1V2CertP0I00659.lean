import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=659
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=260 profileIndexed=true rawInventoryTable=true
    orbit=7179dc8fd9fc92e2
    compact_lrat_sha256=362f52a3c4b447bc7d32b46dcde67030a5f1d35b5c72b07ef6a43f7dd89b9d48
    raw_lrat_sha256=9e90f37460c469088441e028afeed320ac217743b258ba27f5db8c300bd3fe30
    cnf_sha256=8ede2d583f2e2aa8e27c2c3d487caef62974804e6cb0a2539e81e127900ed826
    binary_lrat_sha256=e9b6249c836e9644bc9a13f5bbbc4bf6a45e69a98febb2d05a26c232d92f34a4
    lz4_frame_sha256=55b91edf8a6e0e0d520408714e8d2c2e2e52a9af9e6d083fca1546dfa7b1a190
    packed_lz4_sha256=4e2279d96daf6e35592464373ed27d671fe13060b6e347cd02c456c6f85717f5
    compact_bytes=1046610278 binary_bytes=461832122
    lz4_frame_bytes=280768559 packed_lz4_bytes=320878354
    source_cnf_clauses=613032 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00659Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨659, by native_decide⟩

private def h1V2P0I00659ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/4e/4e2279d96daf6e35592464373ed27d671fe13060b6e347cd02c456c6f85717f5.lrat.lz4p7"

private def h1V2P0I00659RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00659ProofText
    280768559 461832122

private def h1V2P0I00659Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00659Table)
    h1V2P0I00659RawProof).toOption.get!

private theorem h1V2P0I00659Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00659Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00659Table).clauses.toList.all
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
private theorem h1V2P0I00659Check :
    LRAT.check h1V2P0I00659Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00659Table)
        h1V2P0I00659RawProof) := by
  native_decide

theorem h1V2P0I00659Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00659Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00659Nonzero
    h1V2P0I00659RawProof h1V2P0I00659Proof h1V2P0I00659Check

def h1V2P0I00659Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00659Table
  checked := h1V2P0I00659Checked

end Erdos85
