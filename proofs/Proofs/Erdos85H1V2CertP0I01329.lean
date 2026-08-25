import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1329
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=520 profileIndexed=true rawInventoryTable=true
    orbit=dc265cde47b76250
    compact_lrat_sha256=4983267839fe26ea4873d7eb95ed123905250b3a9011a48dc0c39316fa421d69
    raw_lrat_sha256=2d3828808cc2d8d2cb7b420fa50860ff56a700902fb4c33ec271a94e56671f9c
    cnf_sha256=775a8eb800d03d0785ffc80293cc802e422d2e267d6f0aa616979f725518ad27
    binary_lrat_sha256=280def51230c831af88feafab89fec5bb471b245533085f1fe84ded390252d1e
    lz4_frame_sha256=2cacf089561fe9117ca8a9e0798432a2d3a56f9ffc4e65937a9f1a1c0fce6621
    packed_lz4_sha256=9249de762de870f3770b95bf82111b76ba2927ba36b26db0393232473f499f66
    compact_bytes=2215748011 binary_bytes=982284323
    lz4_frame_bytes=558102612 packed_lz4_bytes=637831557
    source_cnf_clauses=613024 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01329Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1329, by native_decide⟩

private def h1V2P0I01329ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/92/9249de762de870f3770b95bf82111b76ba2927ba36b26db0393232473f499f66.lrat.lz4p7"

private def h1V2P0I01329RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01329ProofText
    558102612 982284323

private def h1V2P0I01329Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01329Table)
    h1V2P0I01329RawProof).toOption.get!

private theorem h1V2P0I01329Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01329Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01329Table).clauses.toList.all
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
private theorem h1V2P0I01329Check :
    LRAT.check h1V2P0I01329Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01329Table)
        h1V2P0I01329RawProof) := by
  native_decide

theorem h1V2P0I01329Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01329Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01329Nonzero
    h1V2P0I01329RawProof h1V2P0I01329Proof h1V2P0I01329Check

def h1V2P0I01329Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01329Table
  checked := h1V2P0I01329Checked

end Erdos85
