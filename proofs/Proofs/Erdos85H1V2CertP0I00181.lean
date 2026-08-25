import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=181
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=85 profileIndexed=true rawInventoryTable=true
    orbit=1b3cbdc4c6da4358
    compact_lrat_sha256=1ec09d095273033757a721c861b1d93849332dc8c54f47eb7cef5d2af6751692
    raw_lrat_sha256=18d51a116ecf3ee74398dc5e44a5d808dc5a59f6c33df4c001a853331a91440d
    cnf_sha256=c0c9661c1c802efed4e4e32764cb4b8ac6c6223a41f28c9bb3155931c30d4a83
    binary_lrat_sha256=bc4796e71ca2b7cb638487455ff8bdc4f6eca8b7ad20796766791ad5413df670
    lz4_frame_sha256=06cdaaf7a62d94f91fd9ee032b24218bcae18f16fa380fac23cf99ceb7cf5ca8
    packed_lz4_sha256=99161f903c8ae678d1fa6fb7abebb084a1fdf53562b1603914b54adbecdb43b5
    compact_bytes=950532461 binary_bytes=420208706
    lz4_frame_bytes=251909024 packed_lz4_bytes=287896028
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00181Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨181, by native_decide⟩

private def h1V2P0I00181ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/99/99161f903c8ae678d1fa6fb7abebb084a1fdf53562b1603914b54adbecdb43b5.lrat.lz4p7"

private def h1V2P0I00181RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00181ProofText
    251909024 420208706

private def h1V2P0I00181Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00181Table)
    h1V2P0I00181RawProof).toOption.get!

private theorem h1V2P0I00181Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00181Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00181Table).clauses.toList.all
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
private theorem h1V2P0I00181Check :
    LRAT.check h1V2P0I00181Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00181Table)
        h1V2P0I00181RawProof) := by
  native_decide

theorem h1V2P0I00181Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00181Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00181Nonzero
    h1V2P0I00181RawProof h1V2P0I00181Proof h1V2P0I00181Check

def h1V2P0I00181Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00181Table
  checked := h1V2P0I00181Checked

end Erdos85
