import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1491
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=591 profileIndexed=true rawInventoryTable=true
    orbit=f8ad3e11da8577dd
    compact_lrat_sha256=c71d4bc5d9818e33b19c6f63e980154c5978144771d63e7dda49c4eb85d5b01a
    raw_lrat_sha256=c865331780345a4b80179489788440e19b2b982f51d0660672460158ce0e7be5
    cnf_sha256=9c90863a5587e4cc3948d9f31f2f2de17359405672b486f31a96945f4f57a80c
    binary_lrat_sha256=497448391b5609e66d3d62b8bd1c9c0c05558f0d5c79cab8b0ef4803b7461a37
    lz4_frame_sha256=a286f087b5f9f28f705d6398da6bea0eedf73d26728b57a97e94611170f58741
    packed_lz4_sha256=61c5839ed80b7a8cd72eb00c6af229aa0d99d41e258a7d56e07cccd2b176b3a7
    compact_bytes=1265597716 binary_bytes=561570337
    lz4_frame_bytes=303311894 packed_lz4_bytes=346642165
    source_cnf_clauses=613164 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01491Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1491, by native_decide⟩

private def h1V2P0I01491ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/61/61c5839ed80b7a8cd72eb00c6af229aa0d99d41e258a7d56e07cccd2b176b3a7.lrat.lz4p7"

private def h1V2P0I01491RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01491ProofText
    303311894 561570337

private def h1V2P0I01491Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01491Table)
    h1V2P0I01491RawProof).toOption.get!

private theorem h1V2P0I01491Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01491Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01491Table).clauses.toList.all
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
private theorem h1V2P0I01491Check :
    LRAT.check h1V2P0I01491Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01491Table)
        h1V2P0I01491RawProof) := by
  native_decide

theorem h1V2P0I01491Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01491Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01491Nonzero
    h1V2P0I01491RawProof h1V2P0I01491Proof h1V2P0I01491Check

def h1V2P0I01491Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01491Table
  checked := h1V2P0I01491Checked

end Erdos85
