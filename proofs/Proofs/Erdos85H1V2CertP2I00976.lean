import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=976
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=14
    orbit=3497a66ea5676bb4
    compact_lrat_sha256=521edc9d4fdfb40840e5298514e069b6a6a46aeba3a92c25a5439b604c3b8036
    raw_lrat_sha256=e4573a23312eec711d80b5f894c714d2fc0fade60f7afa5af06ced453ba749ad
    cnf_sha256=66a67c08d3817551a0f5b08721e727ba14be397f05bca5b31c38697277067b60
    binary_lrat_sha256=634c9064ce12d63971e414744ae5825a760ce9fcb07357cac0e31f3a80edd790
    lz4_frame_sha256=6f2a1bcc95e637345eb205f8660ac183f55c7678399d0b712a3f55f13b089ae8
    packed_lz4_sha256=d1ff3a4a7391a80252106f446537f0279dbac2e9dc3c7adebd1d0bfe7c769c8e
    compact_bytes=6749576002 binary_bytes=3048100484
    lz4_frame_bytes=1825103369 packed_lz4_bytes=2085832422
    source_cnf_clauses=610224 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00976Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨14, by native_decide⟩

private def h1V2P2I00976ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/d1/d1ff3a4a7391a80252106f446537f0279dbac2e9dc3c7adebd1d0bfe7c769c8e.lrat.lz4p7"

private def h1V2P2I00976RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00976ProofText
    1825103369 3048100484

private def h1V2P2I00976Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00976Table)
    h1V2P2I00976RawProof).toOption.get!

private theorem h1V2P2I00976Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00976Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00976Table).clauses.toList.all
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
private theorem h1V2P2I00976Check :
    LRAT.check h1V2P2I00976Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00976Table)
        h1V2P2I00976RawProof) := by
  native_decide

theorem h1V2P2I00976Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00976Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00976Nonzero
    h1V2P2I00976RawProof h1V2P2I00976Proof h1V2P2I00976Check

def h1V2P2I00976Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00976Table
  checked := h1V2P2I00976Checked

end Erdos85
