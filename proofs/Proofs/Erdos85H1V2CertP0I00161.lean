import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=161
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=77 profileIndexed=true rawInventoryTable=true
    orbit=18e43ade1dbf7681
    compact_lrat_sha256=92fb1d3c3a45f74403c7857601ddb3b47357c8174cdd64ca69a528b9f4ed50ed
    raw_lrat_sha256=6e0918121ff1bf8533e2e0f3735e4b21501d822852f6865a635adadbee129d1b
    cnf_sha256=ca378fb2893981a864a374254bf0f70a65345378076814085abfa1ef8c62cabe
    binary_lrat_sha256=22f53b3ac98b0a5daf3cb020e9432877f55d31f965d967c383fd012080918e24
    lz4_frame_sha256=9a3ec2a0c4bb53c7721d7c251d138f161d59858f7d33d1eab36a855cf3010070
    packed_lz4_sha256=08ad5c8f225378ced0f00a48a8e331d645783339a0c619667d88f0e8c8478697
    compact_bytes=1477255533 binary_bytes=654809401
    lz4_frame_bytes=362541361 packed_lz4_bytes=414332984
    source_cnf_clauses=613120 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00161Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨161, by native_decide⟩

private def h1V2P0I00161ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/08/08ad5c8f225378ced0f00a48a8e331d645783339a0c619667d88f0e8c8478697.lrat.lz4p7"

private def h1V2P0I00161RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00161ProofText
    362541361 654809401

private def h1V2P0I00161Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00161Table)
    h1V2P0I00161RawProof).toOption.get!

private theorem h1V2P0I00161Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00161Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00161Table).clauses.toList.all
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
private theorem h1V2P0I00161Check :
    LRAT.check h1V2P0I00161Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00161Table)
        h1V2P0I00161RawProof) := by
  native_decide

theorem h1V2P0I00161Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00161Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00161Nonzero
    h1V2P0I00161RawProof h1V2P0I00161Proof h1V2P0I00161Check

def h1V2P0I00161Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00161Table
  checked := h1V2P0I00161Checked

end Erdos85
