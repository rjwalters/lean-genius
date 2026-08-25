import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1125
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=446 profileIndexed=true rawInventoryTable=true
    orbit=bc39b3190c67a00f
    compact_lrat_sha256=fdbaa7f530b0aef067356ba0dbb8a4211a2fda1fa593d782ab7767f895e487e3
    raw_lrat_sha256=cf6243f0521726576152e77e229cf020cb3fd43e56c6498acc9ee22fca7179b2
    cnf_sha256=d3f298a2e8fc8b72d5a50bd8e94ef860e845f24bb0954f24899554287f1207a6
    binary_lrat_sha256=b95bf5e2887f3881f77310cc158523fc3bb132a7b1288d5d73b8f79080be313d
    lz4_frame_sha256=3b5d0b6b321602363ad7476ce5836bc366586203f126016009e3e3b8bb746863
    packed_lz4_sha256=1021238aff2dabcd05acb10e1310ed4423d3ab4fe14469de7ab80f3096722b6d
    compact_bytes=1880447591 binary_bytes=831189616
    lz4_frame_bytes=496973838 packed_lz4_bytes=567970101
    source_cnf_clauses=613072 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01125Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1125, by native_decide⟩

private def h1V2P0I01125ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/10/1021238aff2dabcd05acb10e1310ed4423d3ab4fe14469de7ab80f3096722b6d.lrat.lz4p7"

private def h1V2P0I01125RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01125ProofText
    496973838 831189616

private def h1V2P0I01125Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01125Table)
    h1V2P0I01125RawProof).toOption.get!

private theorem h1V2P0I01125Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01125Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01125Table).clauses.toList.all
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
private theorem h1V2P0I01125Check :
    LRAT.check h1V2P0I01125Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01125Table)
        h1V2P0I01125RawProof) := by
  native_decide

theorem h1V2P0I01125Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01125Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01125Nonzero
    h1V2P0I01125RawProof h1V2P0I01125Proof h1V2P0I01125Check

def h1V2P0I01125Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01125Table
  checked := h1V2P0I01125Checked

end Erdos85
