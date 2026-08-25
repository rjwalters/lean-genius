import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=38
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=19 profileIndexed=true rawInventoryTable=true
    orbit=05b33a6de7aaa520
    compact_lrat_sha256=931f9ebac4aaf7e0e532b504bb25cd7287ef10c11a4a69b42e42bd25232229d8
    raw_lrat_sha256=5c28cfae639d49a1a02c41aea3ea7fda14d9323188679cdd97b5b8eaa890774b
    cnf_sha256=10f5749b3f86acfa15f0c6d37668561a0c3e2e232e1b721b9a9c19739368f541
    binary_lrat_sha256=a0fd7881689d61b5bb4580e2b2bf8f1b9f78cda662d078e1ce47e12c5ba34f6f
    lz4_frame_sha256=2e158d3a51131ed14b6e1c290da50928a49267f8ba0faf3d8bfdccb29af9e59a
    packed_lz4_sha256=4d6662d40801b86bc65755414dda4eab6dc3df60763439408143443e2b1d465d
    compact_bytes=364888300 binary_bytes=159704194
    lz4_frame_bytes=92747055 packed_lz4_bytes=105996635
    source_cnf_clauses=613036 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00038Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨38, by native_decide⟩

private def h1V2P0I00038ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/4d/4d6662d40801b86bc65755414dda4eab6dc3df60763439408143443e2b1d465d.lrat.lz4p7"

private def h1V2P0I00038RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00038ProofText
    92747055 159704194

private def h1V2P0I00038Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00038Table)
    h1V2P0I00038RawProof).toOption.get!

private theorem h1V2P0I00038Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00038Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00038Table).clauses.toList.all
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
private theorem h1V2P0I00038Check :
    LRAT.check h1V2P0I00038Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00038Table)
        h1V2P0I00038RawProof) := by
  native_decide

theorem h1V2P0I00038Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00038Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00038Nonzero
    h1V2P0I00038RawProof h1V2P0I00038Proof h1V2P0I00038Check

def h1V2P0I00038Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00038Table
  checked := h1V2P0I00038Checked

end Erdos85
