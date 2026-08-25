import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=505
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=201 profileIndexed=true rawInventoryTable=true
    orbit=5699eb7ae2367a82
    compact_lrat_sha256=0b43408f1a0736dfb51d427fff6543dbfa2f64f81d4fdb9d771cb60c347d7519
    raw_lrat_sha256=205afe19441d8ed056ba2de70cb038144daf81d78b064775b5a5b40f095c0a09
    cnf_sha256=3426cf68337bf8ad00261659ddad5a52e4dca28af47bcc319bbe68d44269dc62
    binary_lrat_sha256=5ddde578220dcb48e65ad0e31e42675d7f39ab5c8b34cc3154ac6c65fedda308
    lz4_frame_sha256=438e269c123b2c120361b8f6db50f9ec12d7bac75b4e7f9549ee7384f7909195
    packed_lz4_sha256=e0a04bef55ba2cf324315606e3df7adf4953a4ebab7326545a62f9a90b9e287d
    compact_bytes=990273451 binary_bytes=438342002
    lz4_frame_bytes=263580245 packed_lz4_bytes=301234566
    source_cnf_clauses=612916 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00505Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨505, by native_decide⟩

private def h1V2P0I00505ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e0/e0a04bef55ba2cf324315606e3df7adf4953a4ebab7326545a62f9a90b9e287d.lrat.lz4p7"

private def h1V2P0I00505RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00505ProofText
    263580245 438342002

private def h1V2P0I00505Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00505Table)
    h1V2P0I00505RawProof).toOption.get!

private theorem h1V2P0I00505Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00505Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00505Table).clauses.toList.all
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
private theorem h1V2P0I00505Check :
    LRAT.check h1V2P0I00505Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00505Table)
        h1V2P0I00505RawProof) := by
  native_decide

theorem h1V2P0I00505Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00505Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00505Nonzero
    h1V2P0I00505RawProof h1V2P0I00505Proof h1V2P0I00505Check

def h1V2P0I00505Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00505Table
  checked := h1V2P0I00505Checked

end Erdos85
