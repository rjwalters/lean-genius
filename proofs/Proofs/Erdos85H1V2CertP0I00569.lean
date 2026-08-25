import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=569
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=220 profileIndexed=true rawInventoryTable=true
    orbit=6093d3d324c1d4d7
    compact_lrat_sha256=ef47e19c3c8bc47d5a93a7e330b843a39322d03285a45debd01537dce6cfde3d
    raw_lrat_sha256=888eaedf06036bc3c9cf6380794bdf8f444549a8ff62ab49b9bebb0d3bcadb2d
    cnf_sha256=fff1063b2738dc1dbba859de47869566deb0febe6c5d608fbd37df5d5dca779b
    binary_lrat_sha256=ea0dcfd6ef90b37184758500c8f3e4739077dcd3107cc1f55e95ac0ac88a76a5
    lz4_frame_sha256=aa671a697ab81caf4ca6096a68d97d575c128d7397a55a093d854d23f0c43aee
    packed_lz4_sha256=b1ccfccc38f47b91f9c107ceebe8e463ce32ff3d92058b76f7ce40d713ac70c1
    compact_bytes=846509131 binary_bytes=372113805
    lz4_frame_bytes=216936351 packed_lz4_bytes=247927259
    source_cnf_clauses=613146 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00569Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨569, by native_decide⟩

private def h1V2P0I00569ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b1/b1ccfccc38f47b91f9c107ceebe8e463ce32ff3d92058b76f7ce40d713ac70c1.lrat.lz4p7"

private def h1V2P0I00569RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00569ProofText
    216936351 372113805

private def h1V2P0I00569Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00569Table)
    h1V2P0I00569RawProof).toOption.get!

private theorem h1V2P0I00569Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00569Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00569Table).clauses.toList.all
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
private theorem h1V2P0I00569Check :
    LRAT.check h1V2P0I00569Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00569Table)
        h1V2P0I00569RawProof) := by
  native_decide

theorem h1V2P0I00569Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00569Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00569Nonzero
    h1V2P0I00569RawProof h1V2P0I00569Proof h1V2P0I00569Check

def h1V2P0I00569Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00569Table
  checked := h1V2P0I00569Checked

end Erdos85
