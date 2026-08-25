import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1380
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=541 profileIndexed=true rawInventoryTable=true
    orbit=e849040925e548cc
    compact_lrat_sha256=232cff53c862057758514a9ed0c03ed066c77c37f968c291db33ea7966da978a
    raw_lrat_sha256=e5b4c1254e4fadd3e9c908e9464636ea34407e376ed351ebee4b8b1514c06afd
    cnf_sha256=f4d303bc947ff6834add65721f36f935cbff735c838b51875eb53753c8624829
    binary_lrat_sha256=f6b84da2cc71caa76b3dd3c6908be9498b327fe47a61b89279fa4e9d587d5f9f
    lz4_frame_sha256=08a58b358e3fc7c78ce2509497d9614f096ee700d693668ca14b470e72b8a5cf
    packed_lz4_sha256=bcf86a129100a5dc39ad443dda11b0ac8a0548c80cb045858cb58d895c09dceb
    compact_bytes=785386839 binary_bytes=347771316
    lz4_frame_bytes=197950857 packed_lz4_bytes=226229551
    source_cnf_clauses=613148 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01380Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1380, by native_decide⟩

private def h1V2P0I01380ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bc/bcf86a129100a5dc39ad443dda11b0ac8a0548c80cb045858cb58d895c09dceb.lrat.lz4p7"

private def h1V2P0I01380RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01380ProofText
    197950857 347771316

private def h1V2P0I01380Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01380Table)
    h1V2P0I01380RawProof).toOption.get!

private theorem h1V2P0I01380Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01380Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01380Table).clauses.toList.all
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
private theorem h1V2P0I01380Check :
    LRAT.check h1V2P0I01380Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01380Table)
        h1V2P0I01380RawProof) := by
  native_decide

theorem h1V2P0I01380Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01380Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01380Nonzero
    h1V2P0I01380RawProof h1V2P0I01380Proof h1V2P0I01380Check

def h1V2P0I01380Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01380Table
  checked := h1V2P0I01380Checked

end Erdos85
