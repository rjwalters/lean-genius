import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=98
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=46 profileIndexed=true rawInventoryTable=true
    orbit=0f1a95a8dfaf17d4
    compact_lrat_sha256=1649bb1f764d81efdb3497e69b1afbdfc15ced5e4ea05bc0b4194e3c3a4e16b2
    raw_lrat_sha256=515d861275a7a5a73488186bccc36f12fb4e1ac3c04871f9cf2391815b4b1359
    cnf_sha256=622df538a389e5c0ac3035c387a815130b4e8cc22ab563735bf226e15ec63574
    binary_lrat_sha256=6dbca2ce7e729021f767bab48d8e7362639a55c3eac7d36f127e46896eb55279
    lz4_frame_sha256=a5ccb32f26b8ca22698f022e87efaf573ebf57bb5a32aaec25b0e2113ee46947
    packed_lz4_sha256=fcf2f820653d91707aaf6399b0a1b109868ac1c3e2df75b1240b112c78c94451
    compact_bytes=617977452 binary_bytes=271710461
    lz4_frame_bytes=162351677 packed_lz4_bytes=185544774
    source_cnf_clauses=613136 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00098Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨98, by native_decide⟩

private def h1V2P0I00098ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/fc/fcf2f820653d91707aaf6399b0a1b109868ac1c3e2df75b1240b112c78c94451.lrat.lz4p7"

private def h1V2P0I00098RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00098ProofText
    162351677 271710461

private def h1V2P0I00098Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00098Table)
    h1V2P0I00098RawProof).toOption.get!

private theorem h1V2P0I00098Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00098Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00098Table).clauses.toList.all
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
private theorem h1V2P0I00098Check :
    LRAT.check h1V2P0I00098Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00098Table)
        h1V2P0I00098RawProof) := by
  native_decide

theorem h1V2P0I00098Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00098Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00098Nonzero
    h1V2P0I00098RawProof h1V2P0I00098Proof h1V2P0I00098Check

def h1V2P0I00098Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00098Table
  checked := h1V2P0I00098Checked

end Erdos85
