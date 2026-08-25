import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1446
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=567 profileIndexed=true rawInventoryTable=true
    orbit=f17ab4278b1bcd97
    compact_lrat_sha256=5261096545e2b83136fdca25f4575a81e3269d6c6fedbd51701e33c07f74f9e3
    raw_lrat_sha256=f50036729177ffd849757b079b710917cabbb64e6917fa320e1f91d08a256b78
    cnf_sha256=9370225e60c3304857683f3bda82950b2eb3bc7ca60c04f35ee274e78f949138
    binary_lrat_sha256=990096a63e8510c887a85dcfb9b128519482f6178be65d09f66f62d9ccd8f629
    lz4_frame_sha256=c02641ee2c5d6a8b0a267df922653d8e4cf19f784e0beff1c8d0e09ebd4fccfd
    packed_lz4_sha256=aea0a6c9150a5d95dc0ec0ef552689866b12d8472c4cc4519c9a447298ef9d60
    compact_bytes=805438615 binary_bytes=354771852
    lz4_frame_bytes=207275974 packed_lz4_bytes=236886828
    source_cnf_clauses=613256 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01446Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1446, by native_decide⟩

private def h1V2P0I01446ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/ae/aea0a6c9150a5d95dc0ec0ef552689866b12d8472c4cc4519c9a447298ef9d60.lrat.lz4p7"

private def h1V2P0I01446RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01446ProofText
    207275974 354771852

private def h1V2P0I01446Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01446Table)
    h1V2P0I01446RawProof).toOption.get!

private theorem h1V2P0I01446Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01446Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01446Table).clauses.toList.all
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
private theorem h1V2P0I01446Check :
    LRAT.check h1V2P0I01446Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01446Table)
        h1V2P0I01446RawProof) := by
  native_decide

theorem h1V2P0I01446Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01446Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01446Nonzero
    h1V2P0I01446RawProof h1V2P0I01446Proof h1V2P0I01446Check

def h1V2P0I01446Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01446Table
  checked := h1V2P0I01446Checked

end Erdos85
