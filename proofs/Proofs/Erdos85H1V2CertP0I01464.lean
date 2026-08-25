import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1464
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=578 profileIndexed=true rawInventoryTable=true
    orbit=f45dca0206f97dbd
    compact_lrat_sha256=43b7021d578deff44c642b6396e4474cd84917cbc9db070c09feead4ddda1821
    raw_lrat_sha256=292852457280b56a26b90eeafcb393b3a438d1d71fc1f3c513502c449ce8f574
    cnf_sha256=dfa65edcf883ec2023d51137419a167586cdf18c266f4dd784ab19519f47a1ab
    binary_lrat_sha256=6245ef414b5f23e4e1d08427a512aba6b976e223e4e85a9772b228eaaa5a486e
    lz4_frame_sha256=7bf2641fc0b719c776f68e6410636a355b43d565b2d001d6f84b03d510289105
    packed_lz4_sha256=81d55fa1c0d30b8e5bf56f3a56fc948b568f91693d6076beb33dca0b266b6b04
    compact_bytes=1055721425 binary_bytes=468460763
    lz4_frame_bytes=267877313 packed_lz4_bytes=306145501
    source_cnf_clauses=613036 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01464Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1464, by native_decide⟩

private def h1V2P0I01464ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/81/81d55fa1c0d30b8e5bf56f3a56fc948b568f91693d6076beb33dca0b266b6b04.lrat.lz4p7"

private def h1V2P0I01464RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01464ProofText
    267877313 468460763

private def h1V2P0I01464Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01464Table)
    h1V2P0I01464RawProof).toOption.get!

private theorem h1V2P0I01464Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01464Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01464Table).clauses.toList.all
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
private theorem h1V2P0I01464Check :
    LRAT.check h1V2P0I01464Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01464Table)
        h1V2P0I01464RawProof) := by
  native_decide

theorem h1V2P0I01464Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01464Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01464Nonzero
    h1V2P0I01464RawProof h1V2P0I01464Proof h1V2P0I01464Check

def h1V2P0I01464Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01464Table
  checked := h1V2P0I01464Checked

end Erdos85
