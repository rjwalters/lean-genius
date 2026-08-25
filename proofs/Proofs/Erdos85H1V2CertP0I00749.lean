import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=749
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=300 profileIndexed=true rawInventoryTable=true
    orbit=7ee316f50004ef94
    compact_lrat_sha256=991ebd6c7035514f06076a24d08b2b3cd3cca5744777e74e75592d112138ab89
    raw_lrat_sha256=bb2f428db6c08fa6ab80bc6eddaa8b6442426d5cd6590da0756722d25248b085
    cnf_sha256=c0906e5ba38192b7e8454f9c14cc1db771052277c1e49a370c30689d460ab246
    binary_lrat_sha256=b14c4eea426101f83810bf1adb93812cd7e3f731a80d726a498c43b0ac42d0a2
    lz4_frame_sha256=5fadab74d5ff95bd94598648c7bfea7f27e5bf2f712585dedba0d7440a1ab326
    packed_lz4_sha256=040d5c47e589a7a8f5374db7de45b1c4d299372771a2a3ef9567e88a210bd99f
    compact_bytes=1611073873 binary_bytes=710592037
    lz4_frame_bytes=435841325 packed_lz4_bytes=498104372
    source_cnf_clauses=613252 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00749Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨749, by native_decide⟩

private def h1V2P0I00749ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/04/040d5c47e589a7a8f5374db7de45b1c4d299372771a2a3ef9567e88a210bd99f.lrat.lz4p7"

private def h1V2P0I00749RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00749ProofText
    435841325 710592037

private def h1V2P0I00749Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00749Table)
    h1V2P0I00749RawProof).toOption.get!

private theorem h1V2P0I00749Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00749Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00749Table).clauses.toList.all
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
private theorem h1V2P0I00749Check :
    LRAT.check h1V2P0I00749Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00749Table)
        h1V2P0I00749RawProof) := by
  native_decide

theorem h1V2P0I00749Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00749Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00749Nonzero
    h1V2P0I00749RawProof h1V2P0I00749Proof h1V2P0I00749Check

def h1V2P0I00749Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00749Table
  checked := h1V2P0I00749Checked

end Erdos85
