import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=33
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=16 profileIndexed=true rawInventoryTable=true
    orbit=050c8ae009c19043
    compact_lrat_sha256=ae2910de9a77016a185a8732e4b37b43c58966cac8b8bbccbfc99a715523472c
    raw_lrat_sha256=155694f7225daab7786fcb95fd10ca4a72ade70c01a510a5808d3432490e2823
    cnf_sha256=dd629ab18bb67d7ed5649e4366c365fbb035493c91fb2537b958b7d0eff0fc5f
    binary_lrat_sha256=a6d0aa035037c71df4fad5096e4ed05773fd81ab6a9dca51e2c21437e4966998
    lz4_frame_sha256=da9d1dd290617f31c21c38955e15f766dbf2569e22e84a3d8e1c08beeac52125
    packed_lz4_sha256=972871128239c29828c9a2ac8374128233005f76c4cd309bd024bb9a010694ad
    compact_bytes=558324973 binary_bytes=247416131
    lz4_frame_bytes=146039179 packed_lz4_bytes=166901919
    source_cnf_clauses=612892 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00033Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨33, by native_decide⟩

private def h1V2P0I00033ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/97/972871128239c29828c9a2ac8374128233005f76c4cd309bd024bb9a010694ad.lrat.lz4p7"

private def h1V2P0I00033RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00033ProofText
    146039179 247416131

private def h1V2P0I00033Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00033Table)
    h1V2P0I00033RawProof).toOption.get!

private theorem h1V2P0I00033Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00033Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00033Table).clauses.toList.all
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
private theorem h1V2P0I00033Check :
    LRAT.check h1V2P0I00033Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00033Table)
        h1V2P0I00033RawProof) := by
  native_decide

theorem h1V2P0I00033Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00033Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00033Nonzero
    h1V2P0I00033RawProof h1V2P0I00033Proof h1V2P0I00033Check

def h1V2P0I00033Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00033Table
  checked := h1V2P0I00033Checked

end Erdos85
