import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=447
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=180 profileIndexed=true rawInventoryTable=true
    orbit=4d1d540ee07b63b8
    compact_lrat_sha256=e4f064e3015433053a3c56e0135330b4d488179e99e677364396d1b41b50f2d5
    raw_lrat_sha256=e8b5196f7f1682cc4134505152f55578ba88ff45def20879fdb05726a3660bfd
    cnf_sha256=cdd0cf0b2212cb34e354db2e4c8a1f673bb2840fadc64314b32f72d66bf17a91
    binary_lrat_sha256=1f0190825e8a5b6c7f93c75ab39d6b9af5e306128a29069a334728fc12b62649
    lz4_frame_sha256=b84b25a1c8b00accc863487bf6d0b74c2ee697461f879115da17d722001129d5
    packed_lz4_sha256=040ba92a5fd2bc2d1662c4ec6493dcdf8fec42e4e3ad69d8489cd6960719a244
    compact_bytes=1483234846 binary_bytes=653126439
    lz4_frame_bytes=394325155 packed_lz4_bytes=450657320
    source_cnf_clauses=613116 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00447Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨447, by native_decide⟩

private def h1V2P0I00447ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/04/040ba92a5fd2bc2d1662c4ec6493dcdf8fec42e4e3ad69d8489cd6960719a244.lrat.lz4p7"

private def h1V2P0I00447RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00447ProofText
    394325155 653126439

private def h1V2P0I00447Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00447Table)
    h1V2P0I00447RawProof).toOption.get!

private theorem h1V2P0I00447Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00447Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00447Table).clauses.toList.all
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
private theorem h1V2P0I00447Check :
    LRAT.check h1V2P0I00447Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00447Table)
        h1V2P0I00447RawProof) := by
  native_decide

theorem h1V2P0I00447Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00447Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00447Nonzero
    h1V2P0I00447RawProof h1V2P0I00447Proof h1V2P0I00447Check

def h1V2P0I00447Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00447Table
  checked := h1V2P0I00447Checked

end Erdos85
