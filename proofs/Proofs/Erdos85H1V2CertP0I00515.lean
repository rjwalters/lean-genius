import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=515
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=204 profileIndexed=true rawInventoryTable=true
    orbit=5814c24509cdc160
    compact_lrat_sha256=bd7b06fdcab6b0a154cc79772e2e9c8b0ac6b64a54e830d419c01383c076ae5a
    raw_lrat_sha256=9ee670a89ab8356d305c94570c92f618dd5db79f939e3cd870b8bfcad59659b8
    cnf_sha256=4d9db991e9e79392605c7f4fd69cc7aeb6b0e7b0ee68566b90dff238af804a45
    binary_lrat_sha256=01d84c63f1329a7fb51d51989d08ab684950e023f260244e217f0ec89cd40a32
    lz4_frame_sha256=27d4c0a50b7be2322105f7e3fae413f8dc77f62eb5834022b2ea16e7992898f2
    packed_lz4_sha256=99c91597f1400f663c5787792c9406a8fdf4eff55339218311ef6acb24fb9e4a
    compact_bytes=1361306357 binary_bytes=604951041
    lz4_frame_bytes=353589731 packed_lz4_bytes=404102550
    source_cnf_clauses=613228 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00515Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨515, by native_decide⟩

private def h1V2P0I00515ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/99/99c91597f1400f663c5787792c9406a8fdf4eff55339218311ef6acb24fb9e4a.lrat.lz4p7"

private def h1V2P0I00515RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00515ProofText
    353589731 604951041

private def h1V2P0I00515Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00515Table)
    h1V2P0I00515RawProof).toOption.get!

private theorem h1V2P0I00515Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00515Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00515Table).clauses.toList.all
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
private theorem h1V2P0I00515Check :
    LRAT.check h1V2P0I00515Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00515Table)
        h1V2P0I00515RawProof) := by
  native_decide

theorem h1V2P0I00515Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00515Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00515Nonzero
    h1V2P0I00515RawProof h1V2P0I00515Proof h1V2P0I00515Check

def h1V2P0I00515Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00515Table
  checked := h1V2P0I00515Checked

end Erdos85
