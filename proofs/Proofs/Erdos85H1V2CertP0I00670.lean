import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=670
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=267 profileIndexed=true rawInventoryTable=true
    orbit=727796104f975d45
    compact_lrat_sha256=8fc316719ef1c872ef68f1f4f7a14eb7055e8cf397626ce77bc0992d3847c124
    raw_lrat_sha256=7f783244e6f0d3bcc5c66376c0465eaadaf26c11cb10e0a048d6761b76c76461
    cnf_sha256=497d13f82f69e18e26642e679db3f92b4188993e76e4571182097171cabf1f8d
    binary_lrat_sha256=520794e6bb7a04b35bf44f26ed4093bfe2147d73629ddc5f1ea4b65b0fd882dc
    lz4_frame_sha256=2e8a46167813fc5dad1b1bc05d99db7dcc4592ab623b59ebd4e123b7d46fbbe8
    packed_lz4_sha256=e063c5b8d032861b1d212a46d346adb83224f2c6f212d1b7c4e37c13b7bcef9b
    compact_bytes=1037271076 binary_bytes=457205790
    lz4_frame_bytes=266809979 packed_lz4_bytes=304925691
    source_cnf_clauses=613116 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00670Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨670, by native_decide⟩

private def h1V2P0I00670ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e0/e063c5b8d032861b1d212a46d346adb83224f2c6f212d1b7c4e37c13b7bcef9b.lrat.lz4p7"

private def h1V2P0I00670RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00670ProofText
    266809979 457205790

private def h1V2P0I00670Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00670Table)
    h1V2P0I00670RawProof).toOption.get!

private theorem h1V2P0I00670Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00670Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00670Table).clauses.toList.all
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
private theorem h1V2P0I00670Check :
    LRAT.check h1V2P0I00670Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00670Table)
        h1V2P0I00670RawProof) := by
  native_decide

theorem h1V2P0I00670Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00670Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00670Nonzero
    h1V2P0I00670RawProof h1V2P0I00670Proof h1V2P0I00670Check

def h1V2P0I00670Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00670Table
  checked := h1V2P0I00670Checked

end Erdos85
