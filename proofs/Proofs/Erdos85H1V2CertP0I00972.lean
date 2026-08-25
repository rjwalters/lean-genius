import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=972
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=385 profileIndexed=true rawInventoryTable=true
    orbit=a34e8c74aa4490f6
    compact_lrat_sha256=3b228f43a095c55464b0f88224bbe0daf673de6e0e7cbb847a78593ca5482e98
    raw_lrat_sha256=31cf2970353e6f16c3c3b61fbfaa457c11c2e42ff51b92bf63d0b29958d9e942
    cnf_sha256=6a99afa7ccdb748dfc15cf3e8638fbbc7a202fe19b30aab1815fc99b4131b949
    binary_lrat_sha256=572c71e8c1558cfd92a197e76c8b7ae36b529a22a77cdfcc48eee770b0022f69
    lz4_frame_sha256=78a63e68f955dba39538ec5dd647b3f265fb500d6aeed556078d360ab5c4dec2
    packed_lz4_sha256=b079520e7222e04c27790c0f41bd34865f124bc8d8ec4fd65a28754b2908492c
    compact_bytes=2083575643 binary_bytes=925135140
    lz4_frame_bytes=516568200 packed_lz4_bytes=590363658
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00972Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨972, by native_decide⟩

private def h1V2P0I00972ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b0/b079520e7222e04c27790c0f41bd34865f124bc8d8ec4fd65a28754b2908492c.lrat.lz4p7"

private def h1V2P0I00972RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00972ProofText
    516568200 925135140

private def h1V2P0I00972Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00972Table)
    h1V2P0I00972RawProof).toOption.get!

private theorem h1V2P0I00972Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00972Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00972Table).clauses.toList.all
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
private theorem h1V2P0I00972Check :
    LRAT.check h1V2P0I00972Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00972Table)
        h1V2P0I00972RawProof) := by
  native_decide

theorem h1V2P0I00972Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00972Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00972Nonzero
    h1V2P0I00972RawProof h1V2P0I00972Proof h1V2P0I00972Check

def h1V2P0I00972Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00972Table
  checked := h1V2P0I00972Checked

end Erdos85
