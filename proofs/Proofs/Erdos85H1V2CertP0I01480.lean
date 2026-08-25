import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1480
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=585 profileIndexed=true rawInventoryTable=true
    orbit=f6f020ca788662fc
    compact_lrat_sha256=be04f1c6c9cb772fe4fe9d360599603ca17d9f2d336e3666975d4d42efa9b8e4
    raw_lrat_sha256=6b368b243e653b662dcfc7aa17dacf08545a26696b58459aebe2f63a9f5112de
    cnf_sha256=8297880bf046cd0e2bd2cde6fe3243e819c30dce1db00834323ec1d89c3822d6
    binary_lrat_sha256=1b1044be05ba34939268e504b5535e8de6d748110948b71b91724d079467e50b
    lz4_frame_sha256=d39a304a0c606e70b456c881f14c17f0f2e3f703ed6bda56b06795c894ac084d
    packed_lz4_sha256=1d02a7a136c2f9c2af00d1716b7d386cad7bd72343ec511a229d23a4843f9555
    compact_bytes=1357867498 binary_bytes=598654681
    lz4_frame_bytes=354677834 packed_lz4_bytes=405346096
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01480Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1480, by native_decide⟩

private def h1V2P0I01480ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/1d/1d02a7a136c2f9c2af00d1716b7d386cad7bd72343ec511a229d23a4843f9555.lrat.lz4p7"

private def h1V2P0I01480RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01480ProofText
    354677834 598654681

private def h1V2P0I01480Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01480Table)
    h1V2P0I01480RawProof).toOption.get!

private theorem h1V2P0I01480Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01480Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01480Table).clauses.toList.all
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
private theorem h1V2P0I01480Check :
    LRAT.check h1V2P0I01480Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01480Table)
        h1V2P0I01480RawProof) := by
  native_decide

theorem h1V2P0I01480Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01480Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01480Nonzero
    h1V2P0I01480RawProof h1V2P0I01480Proof h1V2P0I01480Check

def h1V2P0I01480Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01480Table
  checked := h1V2P0I01480Checked

end Erdos85
