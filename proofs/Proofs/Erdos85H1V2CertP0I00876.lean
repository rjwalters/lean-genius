import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=876
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=348 profileIndexed=true rawInventoryTable=true
    orbit=92e24b869970a410
    compact_lrat_sha256=dd21478602316b347446941bed3370551fe52d57b962db5c5cf49646c215593f
    raw_lrat_sha256=9b7ece0db69679db3aa3ab3900bf4d39f94c3661044e600c15aaaa9aeaa8bc21
    cnf_sha256=612fd6ef32028acefe8ff72edf144ab2ee972e6ee7e37c4823562c64b663abea
    binary_lrat_sha256=0baaf86fb114e643a3b1fb27ac16bcb7cacc4e538a1aa2834b0a26e3a2eb6a3b
    lz4_frame_sha256=629b54f031d670bd81c4caf1533afee4057eb08ce05af0e1f1684598f82b3e0a
    packed_lz4_sha256=b44f8ff2ddcd0466009d778fcb80885b318f0ec09101519d7e5e58194957572c
    compact_bytes=1737251780 binary_bytes=766088166
    lz4_frame_bytes=445327757 packed_lz4_bytes=508946008
    source_cnf_clauses=613036 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00876Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨876, by native_decide⟩

private def h1V2P0I00876ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b4/b44f8ff2ddcd0466009d778fcb80885b318f0ec09101519d7e5e58194957572c.lrat.lz4p7"

private def h1V2P0I00876RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00876ProofText
    445327757 766088166

private def h1V2P0I00876Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00876Table)
    h1V2P0I00876RawProof).toOption.get!

private theorem h1V2P0I00876Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00876Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00876Table).clauses.toList.all
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
private theorem h1V2P0I00876Check :
    LRAT.check h1V2P0I00876Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00876Table)
        h1V2P0I00876RawProof) := by
  native_decide

theorem h1V2P0I00876Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00876Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00876Nonzero
    h1V2P0I00876RawProof h1V2P0I00876Proof h1V2P0I00876Check

def h1V2P0I00876Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00876Table
  checked := h1V2P0I00876Checked

end Erdos85
