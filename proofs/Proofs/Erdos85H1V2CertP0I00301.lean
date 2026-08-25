import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=301
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=127 profileIndexed=true rawInventoryTable=true
    orbit=3254e4bfa8c9c3fa
    compact_lrat_sha256=c8923d560aad295edbd9e4f5971c7f9050bc68d51be7fba9e034c599b8f30b62
    raw_lrat_sha256=e595d4bf65dde942cd67e02f1c798a12ac410b14262d4f6a5111ab105a1baeb0
    cnf_sha256=13891a003e650a16b7713dd29a7525b33264a69786604a9c04e4bb087269850f
    binary_lrat_sha256=f5cc2a6bfbe02e54f6f1b9e2809d81bd43344bdc18930138063812e3b4be6d0b
    lz4_frame_sha256=92bb90248a803ea09b3f19a6163d39603205a0f882453e5702fea0426919a3c1
    packed_lz4_sha256=e251ebc69e2715d4d72860a0c6cee0fe3e5db3348214f2778787ef01b7a70500
    compact_bytes=503118801 binary_bytes=219722383
    lz4_frame_bytes=125835295 packed_lz4_bytes=143811766
    source_cnf_clauses=613046 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00301Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨301, by native_decide⟩

private def h1V2P0I00301ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e2/e251ebc69e2715d4d72860a0c6cee0fe3e5db3348214f2778787ef01b7a70500.lrat.lz4p7"

private def h1V2P0I00301RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00301ProofText
    125835295 219722383

private def h1V2P0I00301Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00301Table)
    h1V2P0I00301RawProof).toOption.get!

private theorem h1V2P0I00301Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00301Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00301Table).clauses.toList.all
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
private theorem h1V2P0I00301Check :
    LRAT.check h1V2P0I00301Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00301Table)
        h1V2P0I00301RawProof) := by
  native_decide

theorem h1V2P0I00301Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00301Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00301Nonzero
    h1V2P0I00301RawProof h1V2P0I00301Proof h1V2P0I00301Check

def h1V2P0I00301Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00301Table
  checked := h1V2P0I00301Checked

end Erdos85
