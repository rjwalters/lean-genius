import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=156
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=75 profileIndexed=true rawInventoryTable=true
    orbit=175bb1ac2988e083
    compact_lrat_sha256=be109aa62955d186f2b24ea5b30cc5d2f64f926519bb2b723b3d3513c1e7c093
    raw_lrat_sha256=c9384fe057cbfcb6e6da031b18f0580c61dd6602a5869d0c126eb962f863421a
    cnf_sha256=04b2ae91e372d55ad5e377001904ff9b6e5bc50b55d833173b4db206b04ba8f1
    binary_lrat_sha256=94b1ef14e4693b4983f39cd3e5d9024a3063f1fdad525e030ade4c3aefd54fa9
    lz4_frame_sha256=a1e20cb0bf46d47fa9c79e3f1fda3a90fc07fff16d112905410163c42f5fad27
    packed_lz4_sha256=c3bf1e8aea654a4b382a2ce118567acbaaa149ab2e382ab1690de6319523815a
    compact_bytes=896382521 binary_bytes=394700684
    lz4_frame_bytes=227240911 packed_lz4_bytes=259703899
    source_cnf_clauses=613012 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00156Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨156, by native_decide⟩

private def h1V2P0I00156ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/c3/c3bf1e8aea654a4b382a2ce118567acbaaa149ab2e382ab1690de6319523815a.lrat.lz4p7"

private def h1V2P0I00156RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00156ProofText
    227240911 394700684

private def h1V2P0I00156Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00156Table)
    h1V2P0I00156RawProof).toOption.get!

private theorem h1V2P0I00156Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00156Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00156Table).clauses.toList.all
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
private theorem h1V2P0I00156Check :
    LRAT.check h1V2P0I00156Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00156Table)
        h1V2P0I00156RawProof) := by
  native_decide

theorem h1V2P0I00156Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00156Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00156Nonzero
    h1V2P0I00156RawProof h1V2P0I00156Proof h1V2P0I00156Check

def h1V2P0I00156Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00156Table
  checked := h1V2P0I00156Checked

end Erdos85
