import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1428
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=560 profileIndexed=true rawInventoryTable=true
    orbit=ef439c3f2a11ee9e
    compact_lrat_sha256=4136afc98f61dfebe6aac02c6929c4477fb423b0a980dfbb26e598905fed4c48
    raw_lrat_sha256=6e3c9557db5705395a428f706059ce94e7dc2a0bd3d988f580550b713628d79e
    cnf_sha256=fbde648a163020dfd85164b2cd3fcb8019d8913794cb0850ed3b4fbd3d7f3223
    binary_lrat_sha256=90e95faddb6be76dee91bca7d9048d7b8ed61487dde0cff551e7eca66ebad30b
    lz4_frame_sha256=e4740b77007723b7b6b1307f0a488d435865cbcbd1bd527865e7ed71fff165b1
    packed_lz4_sha256=75a7c49927781ca9c61fac3d643e2245163cc239a75eed9d26f2efc008483c6f
    compact_bytes=1035752733 binary_bytes=459114174
    lz4_frame_bytes=271127669 packed_lz4_bytes=309860194
    source_cnf_clauses=613124 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01428Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1428, by native_decide⟩

private def h1V2P0I01428ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/75/75a7c49927781ca9c61fac3d643e2245163cc239a75eed9d26f2efc008483c6f.lrat.lz4p7"

private def h1V2P0I01428RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01428ProofText
    271127669 459114174

private def h1V2P0I01428Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01428Table)
    h1V2P0I01428RawProof).toOption.get!

private theorem h1V2P0I01428Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01428Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01428Table).clauses.toList.all
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
private theorem h1V2P0I01428Check :
    LRAT.check h1V2P0I01428Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01428Table)
        h1V2P0I01428RawProof) := by
  native_decide

theorem h1V2P0I01428Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01428Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01428Nonzero
    h1V2P0I01428RawProof h1V2P0I01428Proof h1V2P0I01428Check

def h1V2P0I01428Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01428Table
  checked := h1V2P0I01428Checked

end Erdos85
