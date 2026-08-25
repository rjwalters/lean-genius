import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1330
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=521 profileIndexed=true rawInventoryTable=true
    orbit=dc5b7dd826fbc82d
    compact_lrat_sha256=5ca74f6b00dd9d0a356ae65c6d56a5ec2982652679b3847337f4b023f298e469
    raw_lrat_sha256=dc9d15c99d9f897b2968b8ed0c845134a7a9c7d5a9ffcb8c5f614eddbdf668ab
    cnf_sha256=249642404eb7f6d67ffd44b1e71d3ca9bae09bdc74ea990c54957198e14f19a6
    binary_lrat_sha256=4f3cb8025fad6bd007f94538e5e8222165ba94f8a699af7c5a5e5b83349a82fb
    lz4_frame_sha256=5df892497d2f63d3cf87017f89a91eb983d204ea940e2f34312fef58dc565fa1
    packed_lz4_sha256=e628f9c0a3263059071f7f3dba4cae150fad9a26bbfe1826f3947dcad6bd94c8
    compact_bytes=1607149889 binary_bytes=708766799
    lz4_frame_bytes=427755977 packed_lz4_bytes=488863974
    source_cnf_clauses=613088 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01330Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1330, by native_decide⟩

private def h1V2P0I01330ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e6/e628f9c0a3263059071f7f3dba4cae150fad9a26bbfe1826f3947dcad6bd94c8.lrat.lz4p7"

private def h1V2P0I01330RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01330ProofText
    427755977 708766799

private def h1V2P0I01330Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01330Table)
    h1V2P0I01330RawProof).toOption.get!

private theorem h1V2P0I01330Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01330Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01330Table).clauses.toList.all
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
private theorem h1V2P0I01330Check :
    LRAT.check h1V2P0I01330Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01330Table)
        h1V2P0I01330RawProof) := by
  native_decide

theorem h1V2P0I01330Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01330Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01330Nonzero
    h1V2P0I01330RawProof h1V2P0I01330Proof h1V2P0I01330Check

def h1V2P0I01330Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01330Table
  checked := h1V2P0I01330Checked

end Erdos85
