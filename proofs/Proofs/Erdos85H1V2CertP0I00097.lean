import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=97
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=45 profileIndexed=true rawInventoryTable=true
    orbit=0f15bd88e1c24a26
    compact_lrat_sha256=faa4cefab81ab5113d717bd10e14dd4ce8d81917d3f56d1260e0efa58d18e5dd
    raw_lrat_sha256=e292e182382c12547b6ca45f5f30a40ef3a29d971aeba3f0d6771b901fd7eb1d
    cnf_sha256=aedeb3837227c8570962c790dad305fe807a07a2c80d6dd8a05ffb3b05302903
    binary_lrat_sha256=fb31b4ded503633f520274987b3ae9705e6092ae87ea333a8ecc1e5e8f996034
    lz4_frame_sha256=cabdd00ef0a28d6803bab134d5cf1504a9156fd8b1aefbb8542ea1138e0e7ed1
    packed_lz4_sha256=55e5eb8f8d4590427cce0ff1fd9884ad4de9764c7a70912212f9be32e0e871c5
    compact_bytes=657944904 binary_bytes=290479415
    lz4_frame_bytes=166652394 packed_lz4_bytes=190459879
    source_cnf_clauses=612940 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00097Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨97, by native_decide⟩

private def h1V2P0I00097ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/55/55e5eb8f8d4590427cce0ff1fd9884ad4de9764c7a70912212f9be32e0e871c5.lrat.lz4p7"

private def h1V2P0I00097RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00097ProofText
    166652394 290479415

private def h1V2P0I00097Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00097Table)
    h1V2P0I00097RawProof).toOption.get!

private theorem h1V2P0I00097Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00097Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00097Table).clauses.toList.all
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
private theorem h1V2P0I00097Check :
    LRAT.check h1V2P0I00097Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00097Table)
        h1V2P0I00097RawProof) := by
  native_decide

theorem h1V2P0I00097Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00097Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00097Nonzero
    h1V2P0I00097RawProof h1V2P0I00097Proof h1V2P0I00097Check

def h1V2P0I00097Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00097Table
  checked := h1V2P0I00097Checked

end Erdos85
