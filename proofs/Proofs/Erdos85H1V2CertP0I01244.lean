import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1244
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=494 profileIndexed=true rawInventoryTable=true
    orbit=cec9e33d5b126f00
    compact_lrat_sha256=e391b9c340d78cc3f206c0d2a06f9e31f663e272a0a7849c72141612d9801e2c
    raw_lrat_sha256=5c31e2f60c7f2fb2237d4b7ac87e7c778f6dc20f6a11815b531fc947e30d253d
    cnf_sha256=2ac2ff0e74b984af6eb71dc8a7f4bb9eba64e34af76bc30637cceacc9e693a8d
    binary_lrat_sha256=9f36f079508befb418951ce253e2aa3a325925321f8852545621449e90d58a3a
    lz4_frame_sha256=5c428dd7e00260ed315a5ca4e0a776cce680651779d4ce6294db37aedd5b5d1f
    packed_lz4_sha256=9214384e24f98de7215c357bb8813cf1afbeb955913091763d1dd087a676b59a
    compact_bytes=1034204105 binary_bytes=460299544
    lz4_frame_bytes=269802319 packed_lz4_bytes=308345508
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01244Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1244, by native_decide⟩

private def h1V2P0I01244ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/92/9214384e24f98de7215c357bb8813cf1afbeb955913091763d1dd087a676b59a.lrat.lz4p7"

private def h1V2P0I01244RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01244ProofText
    269802319 460299544

private def h1V2P0I01244Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01244Table)
    h1V2P0I01244RawProof).toOption.get!

private theorem h1V2P0I01244Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01244Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01244Table).clauses.toList.all
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
private theorem h1V2P0I01244Check :
    LRAT.check h1V2P0I01244Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01244Table)
        h1V2P0I01244RawProof) := by
  native_decide

theorem h1V2P0I01244Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01244Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01244Nonzero
    h1V2P0I01244RawProof h1V2P0I01244Proof h1V2P0I01244Check

def h1V2P0I01244Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01244Table
  checked := h1V2P0I01244Checked

end Erdos85
