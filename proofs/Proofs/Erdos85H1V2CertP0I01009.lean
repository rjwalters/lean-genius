import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1009
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=398 profileIndexed=true rawInventoryTable=true
    orbit=aaac77a7abdec4da
    compact_lrat_sha256=7b24ccc1c3c7a1e49efbc8ced5464a15b19a3c3b2486579e26a0dbdf5e73e6b3
    raw_lrat_sha256=db2485530bb0af130a922515fa66045b123d124d472bb298dcfe404e3889c005
    cnf_sha256=e5529db78487fc872fd7010a223425f73b3a25e0c40716a9e2e44d71508c4280
    binary_lrat_sha256=fb0c1bfd08ba19b53a4930a7d8a1b3698329e8c1b4f5b86a5c289cc59a1e2e95
    lz4_frame_sha256=c3c9f0a5a863506f9ee1e5e7dad89f081c9c2a183b699d2218934177ac53ee59
    packed_lz4_sha256=42e0a41b843669437b54bb5558c385e1eac3f1d6cc50dccb91b7fdba5eaf18ae
    compact_bytes=152985223 binary_bytes=67291522
    lz4_frame_bytes=37934463 packed_lz4_bytes=43353672
    source_cnf_clauses=613054 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01009Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1009, by native_decide⟩

private def h1V2P0I01009ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/42/42e0a41b843669437b54bb5558c385e1eac3f1d6cc50dccb91b7fdba5eaf18ae.lrat.lz4p7"

private def h1V2P0I01009RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01009ProofText
    37934463 67291522

private def h1V2P0I01009Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01009Table)
    h1V2P0I01009RawProof).toOption.get!

private theorem h1V2P0I01009Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01009Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01009Table).clauses.toList.all
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
private theorem h1V2P0I01009Check :
    LRAT.check h1V2P0I01009Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01009Table)
        h1V2P0I01009RawProof) := by
  native_decide

theorem h1V2P0I01009Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01009Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01009Nonzero
    h1V2P0I01009RawProof h1V2P0I01009Proof h1V2P0I01009Check

def h1V2P0I01009Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01009Table
  checked := h1V2P0I01009Checked

end Erdos85
