import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=499
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=198 profileIndexed=true rawInventoryTable=true
    orbit=55f77d6ea8efaae6
    compact_lrat_sha256=26d7ce2fc8320a6bda1939a13557abc86a273dc892cdb217837fca756e669ed0
    raw_lrat_sha256=07242f7ca34b8d04df4024bab91542e3f6fbb81cf619b3b48ceb79e85f98eb02
    cnf_sha256=695d32cd026e6da8d87877b1e12634f55d402fd990c57ff0e9a152af5fb7f191
    binary_lrat_sha256=fe466d1377b56c5160241bc6adc75b8af6bead3b9e7385a27e783225de48af8a
    lz4_frame_sha256=46d0277bffe322af0ea3b97035b86df4adcdc296fdf46900d685f5c7ce4ddc31
    packed_lz4_sha256=6bce27fe589e38390c99d839a819b430bc1dea61c791070f2def74c1af44dd44
    compact_bytes=1116158625 binary_bytes=489433892
    lz4_frame_bytes=265556272 packed_lz4_bytes=303492883
    source_cnf_clauses=613232 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00499Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨499, by native_decide⟩

private def h1V2P0I00499ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6b/6bce27fe589e38390c99d839a819b430bc1dea61c791070f2def74c1af44dd44.lrat.lz4p7"

private def h1V2P0I00499RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00499ProofText
    265556272 489433892

private def h1V2P0I00499Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00499Table)
    h1V2P0I00499RawProof).toOption.get!

private theorem h1V2P0I00499Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00499Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00499Table).clauses.toList.all
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
private theorem h1V2P0I00499Check :
    LRAT.check h1V2P0I00499Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00499Table)
        h1V2P0I00499RawProof) := by
  native_decide

theorem h1V2P0I00499Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00499Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00499Nonzero
    h1V2P0I00499RawProof h1V2P0I00499Proof h1V2P0I00499Check

def h1V2P0I00499Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00499Table
  checked := h1V2P0I00499Checked

end Erdos85
