import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=802
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=319 profileIndexed=true rawInventoryTable=true
    orbit=875b5bd0db56eb5b
    compact_lrat_sha256=674d767b9ee25eb2cdc5121896fd44370f72b60d815984fe8bc2157c9f30d2e4
    raw_lrat_sha256=50a0201369ecb9389f1448f5987bdbb408abb543c1e64d56803394f68aee3b2d
    cnf_sha256=e633ba3ef4f92af9023e7d572862dc3369fe69f42fdaf02aaca4b36b8c1abad1
    binary_lrat_sha256=41554c2217041396d6737d227856e3dc9aee329c2194ba85775f13ab0ff9fb21
    lz4_frame_sha256=cd21a0153824910deca0085d0c7cfaee7285824323a3eea49567d37eeefc176a
    packed_lz4_sha256=a8a641fffc305a984fc8fe1c10f42ee512c2ab17efd59560f505c10c1dddcf66
    compact_bytes=2369157397 binary_bytes=1056052465
    lz4_frame_bytes=616717532 packed_lz4_bytes=704820037
    source_cnf_clauses=613240 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00802Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨802, by native_decide⟩

private def h1V2P0I00802ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a8/a8a641fffc305a984fc8fe1c10f42ee512c2ab17efd59560f505c10c1dddcf66.lrat.lz4p7"

private def h1V2P0I00802RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00802ProofText
    616717532 1056052465

private def h1V2P0I00802Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00802Table)
    h1V2P0I00802RawProof).toOption.get!

private theorem h1V2P0I00802Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00802Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00802Table).clauses.toList.all
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
private theorem h1V2P0I00802Check :
    LRAT.check h1V2P0I00802Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00802Table)
        h1V2P0I00802RawProof) := by
  native_decide

theorem h1V2P0I00802Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00802Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00802Nonzero
    h1V2P0I00802RawProof h1V2P0I00802Proof h1V2P0I00802Check

def h1V2P0I00802Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00802Table
  checked := h1V2P0I00802Checked

end Erdos85
