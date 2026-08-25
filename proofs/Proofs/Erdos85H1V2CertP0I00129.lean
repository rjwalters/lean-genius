import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=129
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=59 profileIndexed=true rawInventoryTable=true
    orbit=13ba48474f6ade75
    compact_lrat_sha256=91da361f8f12fe640db205b9559603fa45cdb85573133091d4b9cf1afe050e07
    raw_lrat_sha256=c09f1ccb3f79dd41f51543ee81138800a27a657278f4d1ada5888843dfb479ab
    cnf_sha256=0a10c001301d6271edeed0f1e663702aed52ddab5750bcf87d68dca723e85090
    binary_lrat_sha256=44179caeaad9ca82a5382cff4d84bbccc947710f6604cac8454e22137e096fb3
    lz4_frame_sha256=8a2dc2215acb86995ded2d587bb5a0334f6195b1a9fe0f78f2bdee521690e077
    packed_lz4_sha256=b70b7b3f9207415b40913581237c61e1470866923dd935ad0858574bf15ba8a8
    compact_bytes=449178406 binary_bytes=196878747
    lz4_frame_bytes=112794746 packed_lz4_bytes=128908282
    source_cnf_clauses=612940 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00129Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨129, by native_decide⟩

private def h1V2P0I00129ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b7/b70b7b3f9207415b40913581237c61e1470866923dd935ad0858574bf15ba8a8.lrat.lz4p7"

private def h1V2P0I00129RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00129ProofText
    112794746 196878747

private def h1V2P0I00129Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00129Table)
    h1V2P0I00129RawProof).toOption.get!

private theorem h1V2P0I00129Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00129Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00129Table).clauses.toList.all
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
private theorem h1V2P0I00129Check :
    LRAT.check h1V2P0I00129Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00129Table)
        h1V2P0I00129RawProof) := by
  native_decide

theorem h1V2P0I00129Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00129Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00129Nonzero
    h1V2P0I00129RawProof h1V2P0I00129Proof h1V2P0I00129Check

def h1V2P0I00129Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00129Table
  checked := h1V2P0I00129Checked

end Erdos85
