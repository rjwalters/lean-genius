import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=850
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=336 profileIndexed=true rawInventoryTable=true
    orbit=8f9f610ef09e770c
    compact_lrat_sha256=cb23ccafe63b2d11d9acfea2c2af575fc5a5a611ab70ff34626cc0d051f90f5f
    raw_lrat_sha256=c0dd36c2ed04685d3ab3a2cc6c58e35ceaa4495c93ac0dbc15873795cf9cba99
    cnf_sha256=73443f14e4b827cae71437242271b6a443c33e0a8ecdac758960d2e9c11b5247
    binary_lrat_sha256=3c974cb535ecaa0df7c86ba275e1e3115b2e351870af5e3c75f0900b67e5688c
    lz4_frame_sha256=aa3910b4c7d7ee1152f926c4aa7c0cdec7050743fd9092485ec877be6b61b68b
    packed_lz4_sha256=d0094c303a943f2dfc0326445adf0a00e9b2beaaa61141b6d135143ff134d262
    compact_bytes=874896702 binary_bytes=385311964
    lz4_frame_bytes=235122699 packed_lz4_bytes=268711656
    source_cnf_clauses=613208 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00850Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨850, by native_decide⟩

private def h1V2P0I00850ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/d0/d0094c303a943f2dfc0326445adf0a00e9b2beaaa61141b6d135143ff134d262.lrat.lz4p7"

private def h1V2P0I00850RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00850ProofText
    235122699 385311964

private def h1V2P0I00850Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00850Table)
    h1V2P0I00850RawProof).toOption.get!

private theorem h1V2P0I00850Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00850Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00850Table).clauses.toList.all
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
private theorem h1V2P0I00850Check :
    LRAT.check h1V2P0I00850Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00850Table)
        h1V2P0I00850RawProof) := by
  native_decide

theorem h1V2P0I00850Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00850Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00850Nonzero
    h1V2P0I00850RawProof h1V2P0I00850Proof h1V2P0I00850Check

def h1V2P0I00850Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00850Table
  checked := h1V2P0I00850Checked

end Erdos85
