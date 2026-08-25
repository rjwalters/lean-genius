import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=4 localIndex=800
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=274 profileIndexed=true rawInventoryTable=true
    orbit=f3175e183b36012f
    compact_lrat_sha256=79e206617ccad87c80905e4f573579aa9bf7a45a8857f1d8830ca6c402e929a5
    raw_lrat_sha256=3dfdb9909642b3d9820c445ccdaaeb741fe3a851e22cc671d7e9d5b97f3b7d66
    cnf_sha256=9493ee00c18a62c4945dbdee9fdc25682d717faa897c945ef9d0278f794065e2
    binary_lrat_sha256=0b19b46271b3304532e119984c5be42aa1f34e8201e6d1a05a69a076e180342b
    lz4_frame_sha256=5372a2936088772176beda5b648584f2328d7407730de6e0af2b6ecbe7a3791d
    packed_lz4_sha256=6df755534939762ae49bba9f758741088ba5dee242f93995ecd924b77097c2ed
    compact_bytes=1865239676 binary_bytes=819930503
    lz4_frame_bytes=454957874 packed_lz4_bytes=519951856
    source_cnf_clauses=607506 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P4I00800Table : OneHighMissTable :=
  (oneHighInventoryTables (4 : Fin 5)).get
    ⟨800, by native_decide⟩

private def h1V2P4I00800ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/6d/6df755534939762ae49bba9f758741088ba5dee242f93995ecd924b77097c2ed.lrat.lz4p7"

private def h1V2P4I00800RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P4I00800ProofText
    454957874 819930503

private def h1V2P4I00800Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 4 h1V2P4I00800Table)
    h1V2P4I00800RawProof).toOption.get!

private theorem h1V2P4I00800Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 4 h1V2P4I00800Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 4 h1V2P4I00800Table).clauses.toList.all
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
private theorem h1V2P4I00800Check :
    LRAT.check h1V2P4I00800Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 4 h1V2P4I00800Table)
        h1V2P4I00800RawProof) := by
  native_decide

theorem h1V2P4I00800Checked :
    OneHighFamilyV2CheckedUnsat 4 h1V2P4I00800Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P4I00800Nonzero
    h1V2P4I00800RawProof h1V2P4I00800Proof h1V2P4I00800Check

def h1V2P4I00800Entry : OneHighFamilyV2CheckedEntry 4 where
  table := h1V2P4I00800Table
  checked := h1V2P4I00800Checked

end Erdos85
