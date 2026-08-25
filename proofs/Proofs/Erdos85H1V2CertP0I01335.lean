import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1335
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=524 profileIndexed=true rawInventoryTable=true
    orbit=dd2a353591b82de9
    compact_lrat_sha256=12b928921ad7f7f5872185e7529bda58a8abeaf04cea81e3b05df2236072ca75
    raw_lrat_sha256=84d7865bb8171306d6f944e666a70fbcbc2f926b2c2498b91fb85cc611d9e69f
    cnf_sha256=255040415e77f62053fc29d404f691ffd02f244243d12e809d48634e37bee690
    binary_lrat_sha256=14125aadb609ef9bce1c5159893428a2e04e3eee3b4e64210f1d42ff9dcd18f5
    lz4_frame_sha256=c9c03b579e987ac8c3d6f4c26b0bf54d6bc0378fb78b957a82b319df2b695c8f
    packed_lz4_sha256=5a739517528251ee0f3aa803d5d83f4c5fbae4c0a01dde781a2f7057160b0678
    compact_bytes=977366136 binary_bytes=430445109
    lz4_frame_bytes=259413372 packed_lz4_bytes=296472426
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01335Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1335, by native_decide⟩

private def h1V2P0I01335ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/5a/5a739517528251ee0f3aa803d5d83f4c5fbae4c0a01dde781a2f7057160b0678.lrat.lz4p7"

private def h1V2P0I01335RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01335ProofText
    259413372 430445109

private def h1V2P0I01335Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01335Table)
    h1V2P0I01335RawProof).toOption.get!

private theorem h1V2P0I01335Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01335Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01335Table).clauses.toList.all
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
private theorem h1V2P0I01335Check :
    LRAT.check h1V2P0I01335Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01335Table)
        h1V2P0I01335RawProof) := by
  native_decide

theorem h1V2P0I01335Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01335Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01335Nonzero
    h1V2P0I01335RawProof h1V2P0I01335Proof h1V2P0I01335Check

def h1V2P0I01335Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01335Table
  checked := h1V2P0I01335Checked

end Erdos85
