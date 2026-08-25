import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1246
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=496 profileIndexed=true rawInventoryTable=true
    orbit=cf0b53914e729513
    compact_lrat_sha256=b786681890c31ff0677ec06c2a9ea6bd3048083e6aeef4dfd1150504cdac3035
    raw_lrat_sha256=aeba7b017c67030c4a94c2cbdcf12420664f0186878b2030a28097e4f462fb8a
    cnf_sha256=769424d5d7a198447a8ba18bce273a00fa736c07b921c3aec80b21f6ff1b5788
    binary_lrat_sha256=fb84bd20c8d4f0505cd76d8b08e9c63abb1c9b8cb94caa659020503aa9c95ffc
    lz4_frame_sha256=a5012d6f632233afb8f388f01f445a582b9719b410096e4316fe77a613d2bb15
    packed_lz4_sha256=b23d7675cfeb60a71e1388043907082f1c87db6c37b3408fde9142f975eb8c1a
    compact_bytes=1116336690 binary_bytes=494544331
    lz4_frame_bytes=278480213 packed_lz4_bytes=318263101
    source_cnf_clauses=612940 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01246Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1246, by native_decide⟩

private def h1V2P0I01246ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b2/b23d7675cfeb60a71e1388043907082f1c87db6c37b3408fde9142f975eb8c1a.lrat.lz4p7"

private def h1V2P0I01246RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01246ProofText
    278480213 494544331

private def h1V2P0I01246Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01246Table)
    h1V2P0I01246RawProof).toOption.get!

private theorem h1V2P0I01246Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01246Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01246Table).clauses.toList.all
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
private theorem h1V2P0I01246Check :
    LRAT.check h1V2P0I01246Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01246Table)
        h1V2P0I01246RawProof) := by
  native_decide

theorem h1V2P0I01246Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01246Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01246Nonzero
    h1V2P0I01246RawProof h1V2P0I01246Proof h1V2P0I01246Check

def h1V2P0I01246Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01246Table
  checked := h1V2P0I01246Checked

end Erdos85
