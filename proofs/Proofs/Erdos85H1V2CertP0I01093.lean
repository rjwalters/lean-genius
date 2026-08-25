import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1093
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=434 profileIndexed=true rawInventoryTable=true
    orbit=b79d934c20ea7c2a
    compact_lrat_sha256=bc456097b6807e5c07a467b4b68ec1fdcabbe86146a9aaa7f9e4cbddb0513907
    raw_lrat_sha256=9b2f712807afd0faee4ec24e4033938c06762ffa41656e762d63709013aae58f
    cnf_sha256=941d2577c5434032208ee90f21855edd28fdc030ee3f2ac8c7b1963c4adf5f27
    binary_lrat_sha256=526d00513c0ca948487b079e81ca4cf07bc6084ad264f73783e4285b9e939c33
    lz4_frame_sha256=5992ba821623b3f5f5ebe7a98c7dc44447bbb2afa95f32b64ff97dde9c4e436d
    packed_lz4_sha256=6544da20a9c14c883f097b6e14e08cad5274dd21bcacee958d9659c566f05a15
    compact_bytes=429230998 binary_bytes=187892477
    lz4_frame_bytes=111003450 packed_lz4_bytes=126861086
    source_cnf_clauses=612972 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01093Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1093, by native_decide⟩

private def h1V2P0I01093ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/65/6544da20a9c14c883f097b6e14e08cad5274dd21bcacee958d9659c566f05a15.lrat.lz4p7"

private def h1V2P0I01093RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01093ProofText
    111003450 187892477

private def h1V2P0I01093Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01093Table)
    h1V2P0I01093RawProof).toOption.get!

private theorem h1V2P0I01093Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01093Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01093Table).clauses.toList.all
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
private theorem h1V2P0I01093Check :
    LRAT.check h1V2P0I01093Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01093Table)
        h1V2P0I01093RawProof) := by
  native_decide

theorem h1V2P0I01093Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01093Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01093Nonzero
    h1V2P0I01093RawProof h1V2P0I01093Proof h1V2P0I01093Check

def h1V2P0I01093Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01093Table
  checked := h1V2P0I01093Checked

end Erdos85
