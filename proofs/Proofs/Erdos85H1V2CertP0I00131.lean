import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=131
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=60 profileIndexed=true rawInventoryTable=true
    orbit=13ff1db611d58a47
    compact_lrat_sha256=5c2f2a63d6ae22a8718d05b6d36c8a8365f2a41f2d690e94e750400e47ef6ee1
    raw_lrat_sha256=d9d1054fd852c80f966748c81c72d3a401cc2dbdd3286ecbf1b30b7c6e96942c
    cnf_sha256=c60aa18d800380d02510fc09f48c79a293c52976fac9256272667fd0e7a4de7e
    binary_lrat_sha256=e55ae4b1154a3d7ad8a0db292dffdc281b802d83459618c6177c22b01af678c0
    lz4_frame_sha256=f94dccf9d39501b9301a94b2ddb76fc36472f2f71828d677949a673f613ab198
    packed_lz4_sha256=a550945c5d078344cd30e8fa7d7ba3856a5269c27c78681fe8b8889f9e07e46e
    compact_bytes=1603568173 binary_bytes=706856339
    lz4_frame_bytes=421811188 packed_lz4_bytes=482069930
    source_cnf_clauses=613100 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00131Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨131, by native_decide⟩

private def h1V2P0I00131ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a5/a550945c5d078344cd30e8fa7d7ba3856a5269c27c78681fe8b8889f9e07e46e.lrat.lz4p7"

private def h1V2P0I00131RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00131ProofText
    421811188 706856339

private def h1V2P0I00131Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00131Table)
    h1V2P0I00131RawProof).toOption.get!

private theorem h1V2P0I00131Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00131Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00131Table).clauses.toList.all
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
private theorem h1V2P0I00131Check :
    LRAT.check h1V2P0I00131Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00131Table)
        h1V2P0I00131RawProof) := by
  native_decide

theorem h1V2P0I00131Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00131Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00131Nonzero
    h1V2P0I00131RawProof h1V2P0I00131Proof h1V2P0I00131Check

def h1V2P0I00131Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00131Table
  checked := h1V2P0I00131Checked

end Erdos85
