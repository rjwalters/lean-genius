import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=928
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=369 profileIndexed=true rawInventoryTable=true
    orbit=9c3c487d9ef4f812
    compact_lrat_sha256=2a698e2db6bff6d43c5ea761c38ef25d545f44b2f07072fddc5ce830b88e7586
    raw_lrat_sha256=4fdf6bc3eabda014828e017333959cc59d083616addccd301ea6f88f7a72e649
    cnf_sha256=bc8283dc51c77c8bff3f9f10da8beb5daffdc641962caed54f86c7a2de7b62e1
    binary_lrat_sha256=12b3168d3ef861e5d38fb76b87c9181e777e325b20b450f450b21cc81c958161
    lz4_frame_sha256=98eb46759897a24df2de97ea7ffc74d41edb19dd1b42679c72d10d0436241d3d
    packed_lz4_sha256=ad9d6099c195784e5409ad2cf0cea23d3b602ba1b251668fa66c6b0910ce7e47
    compact_bytes=1039915789 binary_bytes=457753121
    lz4_frame_bytes=281228842 packed_lz4_bytes=321404391
    source_cnf_clauses=613104 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00928Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨928, by native_decide⟩

private def h1V2P0I00928ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/ad/ad9d6099c195784e5409ad2cf0cea23d3b602ba1b251668fa66c6b0910ce7e47.lrat.lz4p7"

private def h1V2P0I00928RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00928ProofText
    281228842 457753121

private def h1V2P0I00928Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00928Table)
    h1V2P0I00928RawProof).toOption.get!

private theorem h1V2P0I00928Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00928Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00928Table).clauses.toList.all
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
private theorem h1V2P0I00928Check :
    LRAT.check h1V2P0I00928Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00928Table)
        h1V2P0I00928RawProof) := by
  native_decide

theorem h1V2P0I00928Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00928Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00928Nonzero
    h1V2P0I00928RawProof h1V2P0I00928Proof h1V2P0I00928Check

def h1V2P0I00928Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00928Table
  checked := h1V2P0I00928Checked

end Erdos85
