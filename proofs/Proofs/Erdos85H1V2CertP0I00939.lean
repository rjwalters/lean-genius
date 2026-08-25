import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=939
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=373 profileIndexed=true rawInventoryTable=true
    orbit=9e22cd71a27e49a6
    compact_lrat_sha256=1a9e6d09fabd98c65c3e04f8fe945867eea4313852c8dc92801f114b1eb155c4
    raw_lrat_sha256=3b0bc3d45bcdf34dc546e07b92178e9d886b0c22ffaccad5b66a1b7d95a4bcdd
    cnf_sha256=d25cc874e755ebf6d8f006b43127fad3c51abf6657fbe06d0b0ae1f11aaccaee
    binary_lrat_sha256=c301f8b5e92fd6007ee1af6768206c365db20f1b8642d22155d2b5b5d9906f8b
    lz4_frame_sha256=488edd17ba4f209016e6578a9f26aee3c55ac4aa84c338fc351605028f9c58ca
    packed_lz4_sha256=45c701084f57787b31458c4b32c46c6eadbba2338c02de7b69435ad7c4691629
    compact_bytes=1622434701 binary_bytes=715985295
    lz4_frame_bytes=413476888 packed_lz4_bytes=472545015
    source_cnf_clauses=613244 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00939Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨939, by native_decide⟩

private def h1V2P0I00939ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/45/45c701084f57787b31458c4b32c46c6eadbba2338c02de7b69435ad7c4691629.lrat.lz4p7"

private def h1V2P0I00939RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00939ProofText
    413476888 715985295

private def h1V2P0I00939Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00939Table)
    h1V2P0I00939RawProof).toOption.get!

private theorem h1V2P0I00939Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00939Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00939Table).clauses.toList.all
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
private theorem h1V2P0I00939Check :
    LRAT.check h1V2P0I00939Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00939Table)
        h1V2P0I00939RawProof) := by
  native_decide

theorem h1V2P0I00939Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00939Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00939Nonzero
    h1V2P0I00939RawProof h1V2P0I00939Proof h1V2P0I00939Check

def h1V2P0I00939Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00939Table
  checked := h1V2P0I00939Checked

end Erdos85
