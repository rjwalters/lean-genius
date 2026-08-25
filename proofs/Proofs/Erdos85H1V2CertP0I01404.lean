import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1404
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=551 profileIndexed=true rawInventoryTable=true
    orbit=ebdc5e749c127971
    compact_lrat_sha256=515faaf8fc1f252a1d88ef98497bbe45381738266638e9eae83e63484a35805d
    raw_lrat_sha256=6a0ae301b0a1043fe2d6f0dd91d691342eedb9fa5ee81527be8b8bd0c43588d5
    cnf_sha256=ed0f9b1f4ba4a3a1b5b69d0aa3066bd88ed9877c9576336f1563f28dbcbfc9a2
    binary_lrat_sha256=2b4b6008a69308449bf6fb852aa0a411b7e1f0bc36d5eb5b84270d4fbef7003a
    lz4_frame_sha256=f24c3542139aeebbabae4e780a9855e7de94419e358833b32cd0f266ef1be5f1
    packed_lz4_sha256=8be5be7cd2dd9b4782823382af570821f1c386e80e11c62a7ab33adef2b79420
    compact_bytes=221954105 binary_bytes=96633562
    lz4_frame_bytes=57423965 packed_lz4_bytes=65627389
    source_cnf_clauses=612812 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01404Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1404, by native_decide⟩

private def h1V2P0I01404ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/8b/8be5be7cd2dd9b4782823382af570821f1c386e80e11c62a7ab33adef2b79420.lrat.lz4p7"

private def h1V2P0I01404RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01404ProofText
    57423965 96633562

private def h1V2P0I01404Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01404Table)
    h1V2P0I01404RawProof).toOption.get!

private theorem h1V2P0I01404Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01404Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01404Table).clauses.toList.all
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
private theorem h1V2P0I01404Check :
    LRAT.check h1V2P0I01404Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01404Table)
        h1V2P0I01404RawProof) := by
  native_decide

theorem h1V2P0I01404Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01404Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01404Nonzero
    h1V2P0I01404RawProof h1V2P0I01404Proof h1V2P0I01404Check

def h1V2P0I01404Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01404Table
  checked := h1V2P0I01404Checked

end Erdos85
