import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=590
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=10
    orbit=201b4ef0e4005164
    compact_lrat_sha256=9e19f8d8237a15a55c41f1e8af4b05bca2127b971e2d5bdb0c6dfa3297799689
    raw_lrat_sha256=48a29cb6fd366d1c262ac52502eafc90d6e0d747f31d5c93e37df622b1f12e67
    cnf_sha256=0c9a67e785dc039a0c6ce23975f58c105e07aa14a65581907309ba9b748b73d4
    binary_lrat_sha256=b45ec32c85bb48141d5e610e76a1e6657ccc497221cd2c394c8d8ff3769dc03a
    lz4_frame_sha256=0afbb925dd9a08b2eaed5b4be66bf2d8302aa71105a7b099dd97566265a65e6c
    packed_lz4_sha256=ac715ca8e01e6d0db636c3a28258b16800c8a7c8d757963af0ac2a5a4b745a85
    compact_bytes=588958624 binary_bytes=262621320
    lz4_frame_bytes=158684508 packed_lz4_bytes=181353724
    source_cnf_clauses=610348 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00590Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨10, by native_decide⟩

private def h1V2P2I00590ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/ac/ac715ca8e01e6d0db636c3a28258b16800c8a7c8d757963af0ac2a5a4b745a85.lrat.lz4p7"

private def h1V2P2I00590RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00590ProofText
    158684508 262621320

private def h1V2P2I00590Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00590Table)
    h1V2P2I00590RawProof).toOption.get!

private theorem h1V2P2I00590Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00590Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00590Table).clauses.toList.all
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
private theorem h1V2P2I00590Check :
    LRAT.check h1V2P2I00590Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00590Table)
        h1V2P2I00590RawProof) := by
  native_decide

theorem h1V2P2I00590Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00590Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00590Nonzero
    h1V2P2I00590RawProof h1V2P2I00590Proof h1V2P2I00590Check

def h1V2P2I00590Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00590Table
  checked := h1V2P2I00590Checked

end Erdos85
