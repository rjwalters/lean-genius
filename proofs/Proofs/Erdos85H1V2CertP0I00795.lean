import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=795
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=316 profileIndexed=true rawInventoryTable=true
    orbit=86bf1417d706b24f
    compact_lrat_sha256=9756cccabdfc0aa09b7df5112e48a5b3fbdf953ad583fed8ae52154b500fa4a2
    raw_lrat_sha256=775524e41adf40cdd9714ff33bfaa3c3405b732d83d70bf40ca9dcff5aae8866
    cnf_sha256=5c48ec7fe50986dc95b9b8b29ca0d28b73938be60eed77abe2b0f41c43bebd97
    binary_lrat_sha256=8907697fc31f53775e7f7d21a60bb95a31e98219033e06611c4eae90954befd8
    lz4_frame_sha256=cbe54bfa37b11a1c6ef243dc4d8d669faf1a8f86f82f5df65d33879ba99e56d6
    packed_lz4_sha256=6ae04bc1c0fa758860d3be60fe02dd4868586c2f637d3ce9c14d03e286e960ca
    compact_bytes=875349493 binary_bytes=385995970
    lz4_frame_bytes=230217822 packed_lz4_bytes=263106083
    source_cnf_clauses=613138 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00795Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨795, by native_decide⟩

private def h1V2P0I00795ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6a/6ae04bc1c0fa758860d3be60fe02dd4868586c2f637d3ce9c14d03e286e960ca.lrat.lz4p7"

private def h1V2P0I00795RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00795ProofText
    230217822 385995970

private def h1V2P0I00795Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00795Table)
    h1V2P0I00795RawProof).toOption.get!

private theorem h1V2P0I00795Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00795Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00795Table).clauses.toList.all
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
private theorem h1V2P0I00795Check :
    LRAT.check h1V2P0I00795Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00795Table)
        h1V2P0I00795RawProof) := by
  native_decide

theorem h1V2P0I00795Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00795Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00795Nonzero
    h1V2P0I00795RawProof h1V2P0I00795Proof h1V2P0I00795Check

def h1V2P0I00795Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00795Table
  checked := h1V2P0I00795Checked

end Erdos85
