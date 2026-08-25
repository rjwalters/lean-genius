import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=330
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=140 profileIndexed=true rawInventoryTable=true
    orbit=360cd80d2b896cc6
    compact_lrat_sha256=c30d912ce68b4877a53edd49787f8a0c752df76ffecabda71a463b7805133279
    raw_lrat_sha256=58670a5dbdb3c24118edf422cf7ddc7aeb8325c6c563bfd5bc0985d006f9848a
    cnf_sha256=47dc4625e1afe3892f35bafae07e8bbe179187db9b004a39c30829e24ff0e8f0
    binary_lrat_sha256=ea637c0d5c1780b425eab0ebd1f2517fcc09f745a26d1c5ccc031c5ee2dbe4c2
    lz4_frame_sha256=4f0df818404b0878bb4b7ccd745e26f41fbf1d9478148107f590fb301675e403
    packed_lz4_sha256=53267219dc0aeef6e6d2ab29816f65954c8ecb3e6d2fb93d2256ab57052f1594
    compact_bytes=1007964279 binary_bytes=441635096
    lz4_frame_bytes=268851732 packed_lz4_bytes=307259123
    source_cnf_clauses=613280 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00330Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨330, by native_decide⟩

private def h1V2P0I00330ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/53/53267219dc0aeef6e6d2ab29816f65954c8ecb3e6d2fb93d2256ab57052f1594.lrat.lz4p7"

private def h1V2P0I00330RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00330ProofText
    268851732 441635096

private def h1V2P0I00330Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00330Table)
    h1V2P0I00330RawProof).toOption.get!

private theorem h1V2P0I00330Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00330Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00330Table).clauses.toList.all
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
private theorem h1V2P0I00330Check :
    LRAT.check h1V2P0I00330Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00330Table)
        h1V2P0I00330RawProof) := by
  native_decide

theorem h1V2P0I00330Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00330Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00330Nonzero
    h1V2P0I00330RawProof h1V2P0I00330Proof h1V2P0I00330Check

def h1V2P0I00330Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00330Table
  checked := h1V2P0I00330Checked

end Erdos85
