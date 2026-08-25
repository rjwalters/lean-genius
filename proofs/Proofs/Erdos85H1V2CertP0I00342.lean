import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=342
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=148 profileIndexed=true rawInventoryTable=true
    orbit=38f05c3705e73b87
    compact_lrat_sha256=b6f317559c2ffc298f935b5991588c62cb30378a4b9c81d4bace9c3fc748a00a
    raw_lrat_sha256=13ca6de47c443e373d901266f16ae8cc0fc74c2ffbc9804c3d731dd91004f614
    cnf_sha256=17aed2fc0db2e2898865edc47ad8a49d2fcec4d5bc339d261d008e8c62a6e7ef
    binary_lrat_sha256=bf2aeb8e3e910fa123819bbabe48f06de4c3e82400e1bc0bd36708ecba7b5727
    lz4_frame_sha256=e6fe15da0c9053331d829ebb857aa57aaeba04496bc7893213d0bd454c25f548
    packed_lz4_sha256=030c4a6f030058e5be99b878bb4a3fc635abdbda7540c78cb55206da7e7565a5
    compact_bytes=1196132044 binary_bytes=528028527
    lz4_frame_bytes=305002957 packed_lz4_bytes=348574808
    source_cnf_clauses=613116 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00342Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨342, by native_decide⟩

private def h1V2P0I00342ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/03/030c4a6f030058e5be99b878bb4a3fc635abdbda7540c78cb55206da7e7565a5.lrat.lz4p7"

private def h1V2P0I00342RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00342ProofText
    305002957 528028527

private def h1V2P0I00342Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00342Table)
    h1V2P0I00342RawProof).toOption.get!

private theorem h1V2P0I00342Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00342Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00342Table).clauses.toList.all
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
private theorem h1V2P0I00342Check :
    LRAT.check h1V2P0I00342Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00342Table)
        h1V2P0I00342RawProof) := by
  native_decide

theorem h1V2P0I00342Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00342Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00342Nonzero
    h1V2P0I00342RawProof h1V2P0I00342Proof h1V2P0I00342Check

def h1V2P0I00342Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00342Table
  checked := h1V2P0I00342Checked

end Erdos85
