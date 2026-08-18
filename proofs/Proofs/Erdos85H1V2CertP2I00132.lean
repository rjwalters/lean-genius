import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=132
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=2
    orbit=06e404ac65ff079b
    compact_lrat_sha256=cc59756ecb28f151aeccafabca1919629e31429b4191f6d1f06859fb0626ec36
    raw_lrat_sha256=2b1d3f07f524410fe5b06bce2670a5b56106373eaaa4daa4d4243eea2c9ebc13
    cnf_sha256=e2f9cb3aca6e017e3db7aa0d2ff3ba9f82cad7180b4d01ec18e2181a11c2a19f
    binary_lrat_sha256=bc55dd39c77b632e969880882dd7df16cead673ef12ace31c9ab1adf3e7a1113
    lz4_frame_sha256=fd479937ecfc2c6777c889a1dfe85282d4a9101a789717d5a2260aff1daf941b
    packed_lz4_sha256=43b7b79ed033cf7d938d5b40a5fb38d915fc979fa9ff0e89d99460a73c744017
    compact_bytes=1568109265 binary_bytes=708994854
    lz4_frame_bytes=429992423 packed_lz4_bytes=491419912
    source_cnf_clauses=610428 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00132Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨2, by native_decide⟩

private def h1V2P2I00132ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/43/43b7b79ed033cf7d938d5b40a5fb38d915fc979fa9ff0e89d99460a73c744017.lrat.lz4p7"

private def h1V2P2I00132RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00132ProofText
    429992423 708994854

private def h1V2P2I00132Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00132Table)
    h1V2P2I00132RawProof).toOption.get!

private theorem h1V2P2I00132Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00132Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00132Table).clauses.toList.all
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
private theorem h1V2P2I00132Check :
    LRAT.check h1V2P2I00132Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00132Table)
        h1V2P2I00132RawProof) := by
  native_decide

theorem h1V2P2I00132Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00132Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00132Nonzero
    h1V2P2I00132RawProof h1V2P2I00132Proof h1V2P2I00132Check

def h1V2P2I00132Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00132Table
  checked := h1V2P2I00132Checked

end Erdos85
