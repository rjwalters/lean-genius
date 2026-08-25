import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1286
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=507 profileIndexed=true rawInventoryTable=true
    orbit=d528845afc930325
    compact_lrat_sha256=259e24d786e174272040b4596ba1c6daa2c36cf8b238df4f4ab1d69bae6be89a
    raw_lrat_sha256=135c737d660d201887727e897fb78f8d2e1b7d67de2a1cb9b2f8b0030acaf6a9
    cnf_sha256=22e1a8c56e6ce70853741b65acdc4484f0b3ac4551318798e98c32f183dec87b
    binary_lrat_sha256=fbae926c541cd732f18ed1edc47cf414952c12ac42d2968b046f1f61fa404449
    lz4_frame_sha256=79c12146d7b982c3d1684ff9811b4b46d0acf0f69fe655484bfd1e7eb9ba5c46
    packed_lz4_sha256=4689dc2cb7e17699b0c3fffa35654e689dd4e62f91a3f161f8a69800a60150ef
    compact_bytes=1402777773 binary_bytes=619270400
    lz4_frame_bytes=373736553 packed_lz4_bytes=427127490
    source_cnf_clauses=613120 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01286Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1286, by native_decide⟩

private def h1V2P0I01286ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/46/4689dc2cb7e17699b0c3fffa35654e689dd4e62f91a3f161f8a69800a60150ef.lrat.lz4p7"

private def h1V2P0I01286RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01286ProofText
    373736553 619270400

private def h1V2P0I01286Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01286Table)
    h1V2P0I01286RawProof).toOption.get!

private theorem h1V2P0I01286Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01286Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01286Table).clauses.toList.all
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
private theorem h1V2P0I01286Check :
    LRAT.check h1V2P0I01286Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01286Table)
        h1V2P0I01286RawProof) := by
  native_decide

theorem h1V2P0I01286Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01286Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01286Nonzero
    h1V2P0I01286RawProof h1V2P0I01286Proof h1V2P0I01286Check

def h1V2P0I01286Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01286Table
  checked := h1V2P0I01286Checked

end Erdos85
