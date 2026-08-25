import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=201
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=92 profileIndexed=true rawInventoryTable=true
    orbit=1eaa49471143b9b1
    compact_lrat_sha256=3574c947ddbf171521bb381240fb95e520f6c6926062acfea03bfff5458ca5e9
    raw_lrat_sha256=84a04aa908544f7b15100239092b5535c2e4498ff37a360005e12821eee8af41
    cnf_sha256=034578761b64d2bf1c3f69bc9064656d703fb12be080c84b23bbc50b05247816
    binary_lrat_sha256=374a1636d9b847f00d52002e7e124f8b1417cfeebe6bf0f80411d72299ca55d0
    lz4_frame_sha256=1fa61d83d0d62d9c8e949a7d58dc4bacd2f2128b9d244771878d0aca1bdce740
    packed_lz4_sha256=feb74aed6b1ceb8c0b31485ce2caeeaaa1bb8ad0a76b5df3cebf42a6560288e8
    compact_bytes=1484309631 binary_bytes=656119452
    lz4_frame_bytes=392130295 packed_lz4_bytes=448148909
    source_cnf_clauses=613068 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00201Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨201, by native_decide⟩

private def h1V2P0I00201ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/fe/feb74aed6b1ceb8c0b31485ce2caeeaaa1bb8ad0a76b5df3cebf42a6560288e8.lrat.lz4p7"

private def h1V2P0I00201RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00201ProofText
    392130295 656119452

private def h1V2P0I00201Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00201Table)
    h1V2P0I00201RawProof).toOption.get!

private theorem h1V2P0I00201Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00201Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00201Table).clauses.toList.all
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
private theorem h1V2P0I00201Check :
    LRAT.check h1V2P0I00201Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00201Table)
        h1V2P0I00201RawProof) := by
  native_decide

theorem h1V2P0I00201Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00201Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00201Nonzero
    h1V2P0I00201RawProof h1V2P0I00201Proof h1V2P0I00201Check

def h1V2P0I00201Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00201Table
  checked := h1V2P0I00201Checked

end Erdos85
