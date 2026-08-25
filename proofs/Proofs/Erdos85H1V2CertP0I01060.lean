import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1060
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=418 profileIndexed=true rawInventoryTable=true
    orbit=b2f3ff70211abe58
    compact_lrat_sha256=595d25ecdd2f0ff4da74a6e7c32b1b407ebd3eb7953ecaa26616d5f649c23470
    raw_lrat_sha256=4b711113d25176ceb1b3299a0bc38638f798222129bed3fc797d81005cc982d8
    cnf_sha256=12cbe09dcb901969f896603f292bde645567f1898b1a1cb7a4855a2a3121e43f
    binary_lrat_sha256=d19d3c7c5d85cc0603d78eefae9122194f6ef7d1dc179207d89316496520eba6
    lz4_frame_sha256=75459324994ea1b396bad625fd8bfedce91dcc5eaa976960aae29d20596de18f
    packed_lz4_sha256=4d9466b01bb4b75d0afb3fedadc166ca66c80f0224a4cbab77755eb2e3df1fa3
    compact_bytes=2320079057 binary_bytes=1025617151
    lz4_frame_bytes=618428030 packed_lz4_bytes=706774892
    source_cnf_clauses=613264 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01060Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1060, by native_decide⟩

private def h1V2P0I01060ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/4d/4d9466b01bb4b75d0afb3fedadc166ca66c80f0224a4cbab77755eb2e3df1fa3.lrat.lz4p7"

private def h1V2P0I01060RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01060ProofText
    618428030 1025617151

private def h1V2P0I01060Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01060Table)
    h1V2P0I01060RawProof).toOption.get!

private theorem h1V2P0I01060Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01060Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01060Table).clauses.toList.all
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
private theorem h1V2P0I01060Check :
    LRAT.check h1V2P0I01060Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01060Table)
        h1V2P0I01060RawProof) := by
  native_decide

theorem h1V2P0I01060Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01060Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01060Nonzero
    h1V2P0I01060RawProof h1V2P0I01060Proof h1V2P0I01060Check

def h1V2P0I01060Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01060Table
  checked := h1V2P0I01060Checked

end Erdos85
