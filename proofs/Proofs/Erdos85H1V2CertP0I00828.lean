import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=828
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=330 profileIndexed=true rawInventoryTable=true
    orbit=8bb3c7856f2530d2
    compact_lrat_sha256=4e052b35820ea9e8444cfdb7b9dd220f8e1800bafd5a43545c34637ed2f3f557
    raw_lrat_sha256=292193b3daff19826e373cd03e4f3ed7797e7a180af95d555fa5981cdd88a798
    cnf_sha256=e21b268255fbe9d81c2a6b12f1bcd56abe7f893b59800ccc3b7f606bec34abb2
    binary_lrat_sha256=d00d3659030d08bc2d694cde8204d45224304788994874b8d025d6f3f3a9fb77
    lz4_frame_sha256=ab5dd83b3ec4eff49d7dd9fda54add2b9bc0536538305c98f9e77db918caea94
    packed_lz4_sha256=6d06b5121ef23bf5998fc223998bae0432dba73fdffaa2d72a4765d69bdd765d
    compact_bytes=1604273023 binary_bytes=707433941
    lz4_frame_bytes=426033795 packed_lz4_bytes=486895766
    source_cnf_clauses=613240 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00828Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨828, by native_decide⟩

private def h1V2P0I00828ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6d/6d06b5121ef23bf5998fc223998bae0432dba73fdffaa2d72a4765d69bdd765d.lrat.lz4p7"

private def h1V2P0I00828RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00828ProofText
    426033795 707433941

private def h1V2P0I00828Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00828Table)
    h1V2P0I00828RawProof).toOption.get!

private theorem h1V2P0I00828Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00828Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00828Table).clauses.toList.all
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
private theorem h1V2P0I00828Check :
    LRAT.check h1V2P0I00828Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00828Table)
        h1V2P0I00828RawProof) := by
  native_decide

theorem h1V2P0I00828Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00828Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00828Nonzero
    h1V2P0I00828RawProof h1V2P0I00828Proof h1V2P0I00828Check

def h1V2P0I00828Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00828Table
  checked := h1V2P0I00828Checked

end Erdos85
