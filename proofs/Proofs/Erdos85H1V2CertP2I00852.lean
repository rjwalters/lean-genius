import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighProfileTwoReciprocalInventoryTerminal


/-! GENERATED exact-v2 certificate stub.
    profile=2 localIndex=852
    terminal_table=Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables terminalIndex=13
    orbit=2e3de27d93a8a51e
    compact_lrat_sha256=a39746107fd2f2022c3cacb1e3d98ac01ca6a4e9111107626565e255c6ad1ac3
    raw_lrat_sha256=11945473f89bc077822a73ae29f2a835122a959eab946f0f0604c08617250580
    cnf_sha256=469cd1bc33116c5154f98557d15fc97bff69ae2112e710244634af038840fcf5
    binary_lrat_sha256=ceb2f302bd615119adacb8766e6125d9c5902c51c31f40b5f7e7d00b90013f4b
    lz4_frame_sha256=7d8aad30b958c3435dd363f8c4d3672858e8ef7086a0c095e941a4e96f7f6b5b
    packed_lz4_sha256=8e1f80878d4c004cc139c23ea69072637c38c05b3f0b81c710b0c83e3d550611
    compact_bytes=959259086 binary_bytes=429107324
    lz4_frame_bytes=261066430 packed_lz4_bytes=298361635
    source_cnf_clauses=610416 -/

namespace Erdos85

open Std.Tactic.BVDecide

def h1V2P2I00852Table : OneHighMissTable :=
  Erdos85.oneHighProfileTwoReciprocalEntryInventoryTables.get
    ⟨13, by native_decide⟩

private def h1V2P2I00852ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile2-reciprocal-78/packed-promotion/packed/8e/8e1f80878d4c004cc139c23ea69072637c38c05b3f0b81c710b0c83e3d550611.lrat.lz4p7"

private def h1V2P2I00852RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P2I00852ProofText
    261066430 429107324

private def h1V2P2I00852Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 2 h1V2P2I00852Table)
    h1V2P2I00852RawProof).toOption.get!

private theorem h1V2P2I00852Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2 h1V2P2I00852Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2 h1V2P2I00852Table).clauses.toList.all
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
private theorem h1V2P2I00852Check :
    LRAT.check h1V2P2I00852Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 2 h1V2P2I00852Table)
        h1V2P2I00852RawProof) := by
  native_decide

theorem h1V2P2I00852Checked :
    OneHighFamilyV2CheckedUnsat 2 h1V2P2I00852Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P2I00852Nonzero
    h1V2P2I00852RawProof h1V2P2I00852Proof h1V2P2I00852Check

def h1V2P2I00852Entry : OneHighFamilyV2CheckedEntry 2 where
  table := h1V2P2I00852Table
  checked := h1V2P2I00852Checked

end Erdos85
