import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=292
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=121 profileIndexed=true rawInventoryTable=true
    orbit=2f0e55a0396d6a79
    compact_lrat_sha256=f13dc95ef03fbbfc365d5eda536e77975f0931df6942118d6159f27a56628643
    raw_lrat_sha256=77b2b9b45a6bda3f464a0ef014f02013e36756cefa284a4c06306aec6a67b449
    cnf_sha256=0f17976de16fc0bfa919c0608d3ab29518d609a4859e1ea20e59658a022667f6
    binary_lrat_sha256=48a9172b7f2b67f767ae3963949892e647c87a59b8d05e2fac6ebdc1155dcc23
    lz4_frame_sha256=4e59b17be6037e2faf6439c2590298a7b5cd39e951bc4917cb7b57dd568d3d04
    packed_lz4_sha256=f95642f7d3127fcd682f686f6a9f2c7d5245a09ee3fd4c7b01d8c3efbb2da5a2
    compact_bytes=949937801 binary_bytes=422290215
    lz4_frame_bytes=252024549 packed_lz4_bytes=288028056
    source_cnf_clauses=613188 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00292Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨292, by native_decide⟩

private def h1V2P0I00292ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/f9/f95642f7d3127fcd682f686f6a9f2c7d5245a09ee3fd4c7b01d8c3efbb2da5a2.lrat.lz4p7"

private def h1V2P0I00292RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00292ProofText
    252024549 422290215

private def h1V2P0I00292Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00292Table)
    h1V2P0I00292RawProof).toOption.get!

private theorem h1V2P0I00292Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00292Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00292Table).clauses.toList.all
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
private theorem h1V2P0I00292Check :
    LRAT.check h1V2P0I00292Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00292Table)
        h1V2P0I00292RawProof) := by
  native_decide

theorem h1V2P0I00292Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00292Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00292Nonzero
    h1V2P0I00292RawProof h1V2P0I00292Proof h1V2P0I00292Check

def h1V2P0I00292Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00292Table
  checked := h1V2P0I00292Checked

end Erdos85
