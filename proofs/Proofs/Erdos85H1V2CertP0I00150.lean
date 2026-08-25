import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=150
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=72 profileIndexed=true rawInventoryTable=true
    orbit=16d6a07f947825ba
    compact_lrat_sha256=741cb5a0e36ad8cdedc5585962c2b58cab2e4f08fdf4a7775f37ed02c898032c
    raw_lrat_sha256=acc3a38799188384d91e6a881fcfcbe0d854636033bb510c5b67229aa2264ef2
    cnf_sha256=6bacf2fe6b67e5300521aa33e8571931fd62665e502a28ce6e19017043e6fe2c
    binary_lrat_sha256=6b42c215452fe342c86663ba6a1c0d85a223293b63f7c3dfd251c15e388d0bfe
    lz4_frame_sha256=8f41fd6197db290fa0e339827f9d93ed0ae2d81b12dc507aa8c762b8627f8c14
    packed_lz4_sha256=84a6422f2253fe9ba28d7d37fc823a3aa235b1d52f8616a85b80f526946b8c27
    compact_bytes=1565207281 binary_bytes=698854955
    lz4_frame_bytes=420799450 packed_lz4_bytes=480913658
    source_cnf_clauses=613028 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00150Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨150, by native_decide⟩

private def h1V2P0I00150ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/84/84a6422f2253fe9ba28d7d37fc823a3aa235b1d52f8616a85b80f526946b8c27.lrat.lz4p7"

private def h1V2P0I00150RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00150ProofText
    420799450 698854955

private def h1V2P0I00150Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00150Table)
    h1V2P0I00150RawProof).toOption.get!

private theorem h1V2P0I00150Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00150Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00150Table).clauses.toList.all
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
private theorem h1V2P0I00150Check :
    LRAT.check h1V2P0I00150Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00150Table)
        h1V2P0I00150RawProof) := by
  native_decide

theorem h1V2P0I00150Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00150Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00150Nonzero
    h1V2P0I00150RawProof h1V2P0I00150Proof h1V2P0I00150Check

def h1V2P0I00150Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00150Table
  checked := h1V2P0I00150Checked

end Erdos85
