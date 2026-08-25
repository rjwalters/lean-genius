import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=898
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=359 profileIndexed=true rawInventoryTable=true
    orbit=96f37d829ea092f4
    compact_lrat_sha256=dceffaa5bd09ae73492a82f13f328718c52ccd1af126bfdbda6074055f99e91d
    raw_lrat_sha256=51aeb26b91c24674728b3f14d914b6f9744fa0a046cf523b865a106332b568a9
    cnf_sha256=9537a38301d804b8993b5604e9fb3ca421a13968e0fdfe5b6dc62511161f3b8c
    binary_lrat_sha256=0a824f76cc09da6820d95b9372cdb11bdd8092246e3ca75a901aa0e91489254a
    lz4_frame_sha256=f0eabcbe73057b525649f0952275e0d3dfd940ba936ac1c73f8299d56c0394b7
    packed_lz4_sha256=a669e1f993ac4459a2a6d2957f175a70e564210120bf2a31f54d4e4b5cda3056
    compact_bytes=2055941034 binary_bytes=918043768
    lz4_frame_bytes=552058053 packed_lz4_bytes=630923490
    source_cnf_clauses=613028 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00898Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨898, by native_decide⟩

private def h1V2P0I00898ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a6/a669e1f993ac4459a2a6d2957f175a70e564210120bf2a31f54d4e4b5cda3056.lrat.lz4p7"

private def h1V2P0I00898RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00898ProofText
    552058053 918043768

private def h1V2P0I00898Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00898Table)
    h1V2P0I00898RawProof).toOption.get!

private theorem h1V2P0I00898Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00898Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00898Table).clauses.toList.all
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
private theorem h1V2P0I00898Check :
    LRAT.check h1V2P0I00898Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00898Table)
        h1V2P0I00898RawProof) := by
  native_decide

theorem h1V2P0I00898Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00898Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00898Nonzero
    h1V2P0I00898RawProof h1V2P0I00898Proof h1V2P0I00898Check

def h1V2P0I00898Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00898Table
  checked := h1V2P0I00898Checked

end Erdos85
