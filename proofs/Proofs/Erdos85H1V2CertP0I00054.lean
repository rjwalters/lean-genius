import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=54
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=24 profileIndexed=true rawInventoryTable=true
    orbit=07d932d6cf4ecf58
    compact_lrat_sha256=26314f1c73417132446fb580576608fb90c6e9b775c929acbccd91c7886bcf19
    raw_lrat_sha256=b211425e87bf841370f1c03b96d653ca676605b1767e980470c0d5f0d82ce302
    cnf_sha256=a91d54882662b0e52402ba7a1492e860a53982b00ce45a70c073f5b828133182
    binary_lrat_sha256=16df43b8d3fe00569e310385c026d7cd093c9ef97d0322242994366ee2238f05
    lz4_frame_sha256=6d4df56114a5feacbd78bff1dea28db48698c7e8cbd8b15dd1406f592345ffbe
    packed_lz4_sha256=a25b72f2a73c38d1105047c23950096b65cab663ae7548e4a34ced0f33a07565
    compact_bytes=2087111193 binary_bytes=927150375
    lz4_frame_bytes=539482744 packed_lz4_bytes=616551708
    source_cnf_clauses=613060 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00054Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨54, by native_decide⟩

private def h1V2P0I00054ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a2/a25b72f2a73c38d1105047c23950096b65cab663ae7548e4a34ced0f33a07565.lrat.lz4p7"

private def h1V2P0I00054RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00054ProofText
    539482744 927150375

private def h1V2P0I00054Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00054Table)
    h1V2P0I00054RawProof).toOption.get!

private theorem h1V2P0I00054Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00054Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00054Table).clauses.toList.all
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
private theorem h1V2P0I00054Check :
    LRAT.check h1V2P0I00054Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00054Table)
        h1V2P0I00054RawProof) := by
  native_decide

theorem h1V2P0I00054Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00054Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00054Nonzero
    h1V2P0I00054RawProof h1V2P0I00054Proof h1V2P0I00054Check

def h1V2P0I00054Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00054Table
  checked := h1V2P0I00054Checked

end Erdos85
