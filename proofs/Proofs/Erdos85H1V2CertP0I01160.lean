import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1160
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=456 profileIndexed=true rawInventoryTable=true
    orbit=c231d433d9d538d7
    compact_lrat_sha256=879103c549c85251d868e7d30f6fe25e3e1452d9b875e3f17e159818d093f8f0
    raw_lrat_sha256=5878f339667e73237854e37f0bd6468ff9856f83a7954d871371e549f261648b
    cnf_sha256=1833b386e24c544630e246c58976f2c43813d95d60482ec6c937aab7d8bbb293
    binary_lrat_sha256=25ebb1e746a9951f63553f80d45e45ce219b307a82f2b279fb401a7394b5307c
    lz4_frame_sha256=216b9bf633f18501700cbb71f31861258e8eef439c4c8173bdfd677086bee868
    packed_lz4_sha256=65e3644ff95e8b2ef3e3f041007d5ccb102808a1ce2d21c3f500d367a223285e
    compact_bytes=281372607 binary_bytes=123747906
    lz4_frame_bytes=70231408 packed_lz4_bytes=80264467
    source_cnf_clauses=613004 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01160Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1160, by native_decide⟩

private def h1V2P0I01160ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/65/65e3644ff95e8b2ef3e3f041007d5ccb102808a1ce2d21c3f500d367a223285e.lrat.lz4p7"

private def h1V2P0I01160RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01160ProofText
    70231408 123747906

private def h1V2P0I01160Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01160Table)
    h1V2P0I01160RawProof).toOption.get!

private theorem h1V2P0I01160Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01160Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01160Table).clauses.toList.all
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
private theorem h1V2P0I01160Check :
    LRAT.check h1V2P0I01160Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01160Table)
        h1V2P0I01160RawProof) := by
  native_decide

theorem h1V2P0I01160Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01160Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01160Nonzero
    h1V2P0I01160RawProof h1V2P0I01160Proof h1V2P0I01160Check

def h1V2P0I01160Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01160Table
  checked := h1V2P0I01160Checked

end Erdos85
