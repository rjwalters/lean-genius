import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=274
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=113 profileIndexed=true rawInventoryTable=true
    orbit=2c22b4969bc68443
    compact_lrat_sha256=ad2a1b506dbe8845a5fd1e5194f264b96d66c46bc5598fc8e52ad5ccf13e9707
    raw_lrat_sha256=e290592056b924ce8ef2bc68a76d0e0364442ec6c479b706058e16b326e46114
    cnf_sha256=b6d0d1a3f46cca7a67d7daaadf49f0641a1b50650228b07537d21371c307bf7d
    binary_lrat_sha256=9e7e8a377db348997a89147722c24cc73fa9fff93db98f7a2d6d3c0a6d53c404
    lz4_frame_sha256=de474a4f13764bcea66462d7d7800d86602b421d23818e28cdca9d7ffb790543
    packed_lz4_sha256=9a7b98e4c86dc49f0629a169d6bbf7247d6a9abddd51ff20aa0861f1c452767b
    compact_bytes=994637001 binary_bytes=436650878
    lz4_frame_bytes=256407943 packed_lz4_bytes=293037650
    source_cnf_clauses=613164 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00274Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨274, by native_decide⟩

private def h1V2P0I00274ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/9a/9a7b98e4c86dc49f0629a169d6bbf7247d6a9abddd51ff20aa0861f1c452767b.lrat.lz4p7"

private def h1V2P0I00274RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00274ProofText
    256407943 436650878

private def h1V2P0I00274Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00274Table)
    h1V2P0I00274RawProof).toOption.get!

private theorem h1V2P0I00274Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00274Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00274Table).clauses.toList.all
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
private theorem h1V2P0I00274Check :
    LRAT.check h1V2P0I00274Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00274Table)
        h1V2P0I00274RawProof) := by
  native_decide

theorem h1V2P0I00274Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00274Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00274Nonzero
    h1V2P0I00274RawProof h1V2P0I00274Proof h1V2P0I00274Check

def h1V2P0I00274Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00274Table
  checked := h1V2P0I00274Checked

end Erdos85
