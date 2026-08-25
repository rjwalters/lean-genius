import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=585
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=227 profileIndexed=true rawInventoryTable=true
    orbit=63250ef8e44408fb
    compact_lrat_sha256=19d58b9c9d7793bdb535bc867557a625840db26da0995039a2decd82ea91734e
    raw_lrat_sha256=051fb9b7a0ec015154aeff15db83259dabeddf8e7e84563bad20b3686d8ceb67
    cnf_sha256=b5db3f1b7e47d10a76364ca263825eb616bafa215916846b2b6fba7df3c2656c
    binary_lrat_sha256=c174c344c8069fdd1ac1e5016b9b1e52bb60cffc2cd65a6ab83c9a12a8a1d8d4
    lz4_frame_sha256=8cb4103010e8bf4329dea02a6b334e31d05507cc51bdce518326b528a2d7a5e8
    packed_lz4_sha256=502baa6cf248d42e002c78eaf9882c9f4949df3c56952b533286d35cf8688650
    compact_bytes=449188672 binary_bytes=197075745
    lz4_frame_bytes=112143688 packed_lz4_bytes=128164215
    source_cnf_clauses=613082 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00585Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨585, by native_decide⟩

private def h1V2P0I00585ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/50/502baa6cf248d42e002c78eaf9882c9f4949df3c56952b533286d35cf8688650.lrat.lz4p7"

private def h1V2P0I00585RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00585ProofText
    112143688 197075745

private def h1V2P0I00585Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00585Table)
    h1V2P0I00585RawProof).toOption.get!

private theorem h1V2P0I00585Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00585Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00585Table).clauses.toList.all
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
private theorem h1V2P0I00585Check :
    LRAT.check h1V2P0I00585Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00585Table)
        h1V2P0I00585RawProof) := by
  native_decide

theorem h1V2P0I00585Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00585Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00585Nonzero
    h1V2P0I00585RawProof h1V2P0I00585Proof h1V2P0I00585Check

def h1V2P0I00585Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00585Table
  checked := h1V2P0I00585Checked

end Erdos85
