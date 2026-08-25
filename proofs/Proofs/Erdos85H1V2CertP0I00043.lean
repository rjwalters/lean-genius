import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=43
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=21 profileIndexed=true rawInventoryTable=true
    orbit=06965a1a7bd94410
    compact_lrat_sha256=4603e991268bd1ffbb4a8f0164feeea143687b423df9d4741e6d67b79e492747
    raw_lrat_sha256=1ed1542c4776b94e79ea593da4952234c69acdee86d13accb80102e160fd54f9
    cnf_sha256=63f9f506a68457247ad6b1ad9ef3d7d40a5e3d4b202503d28f3168c72c4d9dd4
    binary_lrat_sha256=a240f79a62d4214615c52ac9f253d561d93ac969a69a7e421c1a82bc365fcb18
    lz4_frame_sha256=0af28e834f2b1dfcfb145806da0a13504b44297557716c77372e2b5a0658dbd1
    packed_lz4_sha256=2ad0f454f40fd4093244e216ff61d280797cab1b7f71b7ed74cf076180f8b464
    compact_bytes=1141456669 binary_bytes=503273742
    lz4_frame_bytes=293552585 packed_lz4_bytes=335488669
    source_cnf_clauses=613030 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00043Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨43, by native_decide⟩

private def h1V2P0I00043ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/2a/2ad0f454f40fd4093244e216ff61d280797cab1b7f71b7ed74cf076180f8b464.lrat.lz4p7"

private def h1V2P0I00043RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00043ProofText
    293552585 503273742

private def h1V2P0I00043Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00043Table)
    h1V2P0I00043RawProof).toOption.get!

private theorem h1V2P0I00043Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00043Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00043Table).clauses.toList.all
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
private theorem h1V2P0I00043Check :
    LRAT.check h1V2P0I00043Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00043Table)
        h1V2P0I00043RawProof) := by
  native_decide

theorem h1V2P0I00043Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00043Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00043Nonzero
    h1V2P0I00043RawProof h1V2P0I00043Proof h1V2P0I00043Check

def h1V2P0I00043Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00043Table
  checked := h1V2P0I00043Checked

end Erdos85
