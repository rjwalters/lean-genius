import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=437
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=177 profileIndexed=true rawInventoryTable=true
    orbit=4ca1057cd7ff1848
    compact_lrat_sha256=9ee9b61eff838add3cb0bc373f97f24be016c2d4fd9c2f22df50e1433095b407
    raw_lrat_sha256=e6c26e5489d225d9fd46390fe378c92caed1915cf8a14b0c427e46510e92d62c
    cnf_sha256=0c54e80fb80a6e81d1b9c98d0bd8591b3ce92c0d6e6becf85d053e15b411f72a
    binary_lrat_sha256=924ee6b3743352814fd361cdaa53c7f7f07da380bb645591f9ca38a9e7b69fd2
    lz4_frame_sha256=1c8cbc611b181ec6f891e81e63074c41f4b5ef9184b9f0cf330867fedee71fb0
    packed_lz4_sha256=b04b14137b844b411ab5322ee52b308b11ec193f2b5c5f982ffabbb32199e84f
    compact_bytes=1014302875 binary_bytes=452126121
    lz4_frame_bytes=271296771 packed_lz4_bytes=310053453
    source_cnf_clauses=613172 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00437Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨437, by native_decide⟩

private def h1V2P0I00437ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/b0/b04b14137b844b411ab5322ee52b308b11ec193f2b5c5f982ffabbb32199e84f.lrat.lz4p7"

private def h1V2P0I00437RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00437ProofText
    271296771 452126121

private def h1V2P0I00437Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00437Table)
    h1V2P0I00437RawProof).toOption.get!

private theorem h1V2P0I00437Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00437Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00437Table).clauses.toList.all
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
private theorem h1V2P0I00437Check :
    LRAT.check h1V2P0I00437Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00437Table)
        h1V2P0I00437RawProof) := by
  native_decide

theorem h1V2P0I00437Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00437Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00437Nonzero
    h1V2P0I00437RawProof h1V2P0I00437Proof h1V2P0I00437Check

def h1V2P0I00437Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00437Table
  checked := h1V2P0I00437Checked

end Erdos85
