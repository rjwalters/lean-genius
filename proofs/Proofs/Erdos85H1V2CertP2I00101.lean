import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=101
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=1
    orbit=051e2195907600c6
    compact_lrat_sha256=45b7779a1ca3ee141ddac1874e96da857ba020e78688745781fe8dbf5675625c
    raw_lrat_sha256=ab6e53a6dbc95bd6804d66063f08aaa1a62c6fa256f3ae013a406657f7585ec5
    cnf_sha256=f2b1df24b580a14d8e76de3dc239e2070f85769443dd0d1b2bed2d8a34d36e19
    binary_lrat_sha256=2d67375aa686cb429094817798c9e976657c9762c1c8bd534080dd29d15207de
    lz4_frame_sha256=8bc4b4c406344c7590aab433df697c539948141d4ac8df0a582c7fe216da7236
    packed_lz4_sha256=11aac57bea1f3967c36607898e82d3af9f3df230a898d699cdb9b70ca8aae58d
    compact_bytes=1962320946 binary_bytes=884230379
    lz4_frame_bytes=531347363 packed_lz4_bytes=607254130
    source_cnf_clauses=610360 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00101Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨1, by native_decide⟩

private def h1V2P2I00101ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/11/11aac57bea1f3967c36607898e82d3af9f3df230a898d699cdb9b70ca8aae58d.lrat.lz4p7"

private def h1V2P2I00101RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00101ProofText
    531347363 884230379

private def h1V2P2I00101Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00101Table)
    h1V2P2I00101RawProof).toOption.get!

private theorem h1V2P2I00101Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00101Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00101Table).clauses.toList.all
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
private theorem h1V2P2I00101Check :
    LRAT.check h1V2P2I00101Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00101Table)
        h1V2P2I00101RawProof) := by
  native_decide

theorem h1V2P2I00101Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00101Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00101Nonzero
    h1V2P2I00101RawProof h1V2P2I00101Proof h1V2P2I00101Check

def h1V2P2I00101Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00101Table
  checked := h1V2P2I00101Checked

end Erdos85
