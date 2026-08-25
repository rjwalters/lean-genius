import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1179
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=467 profileIndexed=true rawInventoryTable=true
    orbit=c4a4b92150835bc3
    compact_lrat_sha256=ab6aa6346d45e015057d2e8559c924a796e9eada8e2a27a356f7ed41e625ffa4
    raw_lrat_sha256=bcce61b36fe3b87ded3a8205d6c5754bdcac30f1eb5f978d45abce65ea5bf348
    cnf_sha256=08139b07dd54158e7f74e74c6ccc0712fa580a4c8679b8d6caf48737a0349261
    binary_lrat_sha256=caa52e70ef607619b06ab6053bdaf567e949614de7044607b011e02bbe83c689
    lz4_frame_sha256=3bed955e01a0fadd0b3d616ba1973fb9626ee9c85624a565d2f2cac1cf4e2015
    packed_lz4_sha256=05e715000c3aee10df80b600b4c6e1bfdc05d664a429ae330f15cfcd85e076e6
    compact_bytes=630124127 binary_bytes=276894112
    lz4_frame_bytes=161433741 packed_lz4_bytes=184495704
    source_cnf_clauses=613104 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01179Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1179, by native_decide⟩

private def h1V2P0I01179ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/05/05e715000c3aee10df80b600b4c6e1bfdc05d664a429ae330f15cfcd85e076e6.lrat.lz4p7"

private def h1V2P0I01179RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01179ProofText
    161433741 276894112

private def h1V2P0I01179Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01179Table)
    h1V2P0I01179RawProof).toOption.get!

private theorem h1V2P0I01179Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01179Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01179Table).clauses.toList.all
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
private theorem h1V2P0I01179Check :
    LRAT.check h1V2P0I01179Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01179Table)
        h1V2P0I01179RawProof) := by
  native_decide

theorem h1V2P0I01179Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01179Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01179Nonzero
    h1V2P0I01179RawProof h1V2P0I01179Proof h1V2P0I01179Check

def h1V2P0I01179Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01179Table
  checked := h1V2P0I01179Checked

end Erdos85
