import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=562
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=216 profileIndexed=true rawInventoryTable=true
    orbit=5fb60ba52089a11b
    compact_lrat_sha256=c107e3b27a8488fc69d183ee66f1fd862ab56f91ccd3d5289fc2c868aa55f9fe
    raw_lrat_sha256=6cd186e29790aa27337bb11d403999dce0a005853c3bd0da3650dec8ec90496f
    cnf_sha256=68cbc6ea556064cd9ee69877dd0b452cc4bb770dafeb81d07fcb4e6f47295936
    binary_lrat_sha256=0093ea1c8276d2087a0e5bf57dc2b35c34a53519a85a3bb03bedaf6397c419e3
    lz4_frame_sha256=ce12eb3871d9fad58f07a0a194e738b7794d9bce1d63a83954b019c1fe6c9720
    packed_lz4_sha256=498c1194b1861a9846e0fad28d14142158a9d583ed60ba185b18390797dc8cd0
    compact_bytes=1819966626 binary_bytes=808138039
    lz4_frame_bytes=499248273 packed_lz4_bytes=570569455
    source_cnf_clauses=613148 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00562Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨562, by native_decide⟩

private def h1V2P0I00562ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/49/498c1194b1861a9846e0fad28d14142158a9d583ed60ba185b18390797dc8cd0.lrat.lz4p7"

private def h1V2P0I00562RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00562ProofText
    499248273 808138039

private def h1V2P0I00562Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00562Table)
    h1V2P0I00562RawProof).toOption.get!

private theorem h1V2P0I00562Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00562Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00562Table).clauses.toList.all
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
private theorem h1V2P0I00562Check :
    LRAT.check h1V2P0I00562Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00562Table)
        h1V2P0I00562RawProof) := by
  native_decide

theorem h1V2P0I00562Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00562Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00562Nonzero
    h1V2P0I00562RawProof h1V2P0I00562Proof h1V2P0I00562Check

def h1V2P0I00562Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00562Table
  checked := h1V2P0I00562Checked

end Erdos85
