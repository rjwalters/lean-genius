import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1486
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=588 profileIndexed=true rawInventoryTable=true
    orbit=f7df5246bbd8ab3c
    compact_lrat_sha256=d48ba5356723b39663233ea6b6b1fcf14fc845fcf6c07fbb2d39e034f7a5dbca
    raw_lrat_sha256=a793a22be186764b67539bd16450369076596a4f2936ef866700023f95adb9ff
    cnf_sha256=89d0b15969a3dea468ea9a6fd4378c34afab7b5d85c6b039ea292aa0139913f8
    binary_lrat_sha256=b7ddae0607256253b9924b7ced343a9f11cbce84b13b4ae1dbb0caf3bb1b3197
    lz4_frame_sha256=5ac1337766f21944b5441c86443fd3184c25a3f089f9880de885555f1e226808
    packed_lz4_sha256=497c72af0c43b7ab91329e75625d75a92c4077a3d5547622e00a67f2e53e6d29
    compact_bytes=2043554054 binary_bytes=912774218
    lz4_frame_bytes=540927433 packed_lz4_bytes=618202781
    source_cnf_clauses=613100 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01486Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1486, by native_decide⟩

private def h1V2P0I01486ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/49/497c72af0c43b7ab91329e75625d75a92c4077a3d5547622e00a67f2e53e6d29.lrat.lz4p7"

private def h1V2P0I01486RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01486ProofText
    540927433 912774218

private def h1V2P0I01486Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01486Table)
    h1V2P0I01486RawProof).toOption.get!

private theorem h1V2P0I01486Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01486Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01486Table).clauses.toList.all
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
private theorem h1V2P0I01486Check :
    LRAT.check h1V2P0I01486Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01486Table)
        h1V2P0I01486RawProof) := by
  native_decide

theorem h1V2P0I01486Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01486Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01486Nonzero
    h1V2P0I01486RawProof h1V2P0I01486Proof h1V2P0I01486Check

def h1V2P0I01486Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01486Table
  checked := h1V2P0I01486Checked

end Erdos85
