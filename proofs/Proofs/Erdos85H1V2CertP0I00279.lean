import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=279
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=116 profileIndexed=true rawInventoryTable=true
    orbit=2cda46b732a42272
    compact_lrat_sha256=893abe4a320b699116bf76af8f9a209aedf9dc2bb82eeeaf8b4d356e30deee3d
    raw_lrat_sha256=0737d173e7901d648abafd6e76c8b4d94b6270ce2af6cc02940b03074c511db5
    cnf_sha256=1b617d03b82effad32da6377ec65e34963d59d7c992f13b091d6741f6b2f567b
    binary_lrat_sha256=322bfb2a4d02b487f3f999051b7de3398b2c3dc297f80dacb80f1fb7463f6638
    lz4_frame_sha256=dcb4e4d99cc21caa85b7319ee279661302e0d37b1b2d73350bcbecd6531adc0a
    packed_lz4_sha256=bb7370ff564dec21f6c7a5fe5fabb8b4279ef68cb3cfc9fa2e313c9aec1c38ac
    compact_bytes=886707569 binary_bytes=388628602
    lz4_frame_bytes=221785647 packed_lz4_bytes=253469311
    source_cnf_clauses=613060 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00279Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨279, by native_decide⟩

private def h1V2P0I00279ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bb/bb7370ff564dec21f6c7a5fe5fabb8b4279ef68cb3cfc9fa2e313c9aec1c38ac.lrat.lz4p7"

private def h1V2P0I00279RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00279ProofText
    221785647 388628602

private def h1V2P0I00279Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00279Table)
    h1V2P0I00279RawProof).toOption.get!

private theorem h1V2P0I00279Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00279Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00279Table).clauses.toList.all
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
private theorem h1V2P0I00279Check :
    LRAT.check h1V2P0I00279Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00279Table)
        h1V2P0I00279RawProof) := by
  native_decide

theorem h1V2P0I00279Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00279Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00279Nonzero
    h1V2P0I00279RawProof h1V2P0I00279Proof h1V2P0I00279Check

def h1V2P0I00279Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00279Table
  checked := h1V2P0I00279Checked

end Erdos85
