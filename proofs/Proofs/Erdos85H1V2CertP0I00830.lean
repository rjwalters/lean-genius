import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=830
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=331 profileIndexed=true rawInventoryTable=true
    orbit=8bda2faa93a7a455
    compact_lrat_sha256=c095f48d28752641c88615b118d4e6e617137edeca8373965ed48b7f01a24db8
    raw_lrat_sha256=90490d656c414defa6d2bc7a3b6151437ac8899def4cf486a1a412df873014e5
    cnf_sha256=a732cfafe972b6f6ebf7a18ba586c4a3320e2ac37a5e8bd3c735f7e2ef5d6628
    binary_lrat_sha256=3d6d92b0f155ce17205f63df141ac0e6e19b5f768a494f3f5f47dcc8f527787b
    lz4_frame_sha256=7f106c267775a66a1de10ee0b9f8690600e8a636328d1d5250608fe972364fab
    packed_lz4_sha256=ebe78cba6f7828c531631318f560abae65c9d8003fe49013fae42253b0016559
    compact_bytes=921572938 binary_bytes=404565672
    lz4_frame_bytes=239367435 packed_lz4_bytes=273562783
    source_cnf_clauses=613212 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00830Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨830, by native_decide⟩

private def h1V2P0I00830ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/eb/ebe78cba6f7828c531631318f560abae65c9d8003fe49013fae42253b0016559.lrat.lz4p7"

private def h1V2P0I00830RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00830ProofText
    239367435 404565672

private def h1V2P0I00830Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00830Table)
    h1V2P0I00830RawProof).toOption.get!

private theorem h1V2P0I00830Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00830Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00830Table).clauses.toList.all
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
private theorem h1V2P0I00830Check :
    LRAT.check h1V2P0I00830Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00830Table)
        h1V2P0I00830RawProof) := by
  native_decide

theorem h1V2P0I00830Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00830Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00830Nonzero
    h1V2P0I00830RawProof h1V2P0I00830Proof h1V2P0I00830Check

def h1V2P0I00830Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00830Table
  checked := h1V2P0I00830Checked

end Erdos85
