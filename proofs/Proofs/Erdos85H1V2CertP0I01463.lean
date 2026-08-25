import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1463
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=577 profileIndexed=true rawInventoryTable=true
    orbit=f453c90d2c0fb485
    compact_lrat_sha256=720e60f931a59d098fd4c13c1b90533eae57e5bd8a20e4ca5ec26d79a210886c
    raw_lrat_sha256=9da816463f2db6c030dc367a7f9e4ea7db0ad517592011fd35f911d4b8c2681a
    cnf_sha256=cdeba9a5c6854cdc43281daaa218fa16b4d8621ac465c0cc23623fb1b5415a39
    binary_lrat_sha256=808f9669773c9c96671ae56e4f9e88198980c3d37c65597d925a212940893931
    lz4_frame_sha256=8b30f3ff637d03f548d6e7b0b000a924f7d1393ab911227fa166579702c804b0
    packed_lz4_sha256=93869deaaddc9dfc362d3e5a020f1201d37be215b23e51f42eba4315fb14f0f1
    compact_bytes=920470139 binary_bytes=404452618
    lz4_frame_bytes=228415626 packed_lz4_bytes=261046430
    source_cnf_clauses=612812 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01463Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1463, by native_decide⟩

private def h1V2P0I01463ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/93/93869deaaddc9dfc362d3e5a020f1201d37be215b23e51f42eba4315fb14f0f1.lrat.lz4p7"

private def h1V2P0I01463RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01463ProofText
    228415626 404452618

private def h1V2P0I01463Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01463Table)
    h1V2P0I01463RawProof).toOption.get!

private theorem h1V2P0I01463Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01463Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01463Table).clauses.toList.all
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
private theorem h1V2P0I01463Check :
    LRAT.check h1V2P0I01463Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01463Table)
        h1V2P0I01463RawProof) := by
  native_decide

theorem h1V2P0I01463Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01463Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01463Nonzero
    h1V2P0I01463RawProof h1V2P0I01463Proof h1V2P0I01463Check

def h1V2P0I01463Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01463Table
  checked := h1V2P0I01463Checked

end Erdos85
