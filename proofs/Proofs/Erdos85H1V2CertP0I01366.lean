import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1366
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=535 profileIndexed=true rawInventoryTable=true
    orbit=e44bc8dafa62b6a2
    compact_lrat_sha256=9e595bd56d39b78789846aa758d51b604b1b10e2df04920907d037ba636ed515
    raw_lrat_sha256=19adc5616ce26a8475c56d9d47489024fca0984b5a4472aaadcc84b95d3691bf
    cnf_sha256=74f7f5161003a1906046829de7ed1e7632f0faee50218970212045e9ed890fcd
    binary_lrat_sha256=2c3abb60bce72f33146593a42c0575835064e95d953ad0f3d1380fcd7bbdadf0
    lz4_frame_sha256=e282e221a8474f7c77f2b9828610403ba6130f754cee4643dcfd01fd996994bb
    packed_lz4_sha256=465493c4cdd569cc53c9f4c80b1fb18a6fd4c64c319aad97185a8e6a8469d09d
    compact_bytes=1810715882 binary_bytes=801292228
    lz4_frame_bytes=489941500 packed_lz4_bytes=559933143
    source_cnf_clauses=613056 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01366Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1366, by native_decide⟩

private def h1V2P0I01366ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/46/465493c4cdd569cc53c9f4c80b1fb18a6fd4c64c319aad97185a8e6a8469d09d.lrat.lz4p7"

private def h1V2P0I01366RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01366ProofText
    489941500 801292228

private def h1V2P0I01366Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01366Table)
    h1V2P0I01366RawProof).toOption.get!

private theorem h1V2P0I01366Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01366Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01366Table).clauses.toList.all
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
private theorem h1V2P0I01366Check :
    LRAT.check h1V2P0I01366Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01366Table)
        h1V2P0I01366RawProof) := by
  native_decide

theorem h1V2P0I01366Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01366Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01366Nonzero
    h1V2P0I01366RawProof h1V2P0I01366Proof h1V2P0I01366Check

def h1V2P0I01366Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01366Table
  checked := h1V2P0I01366Checked

end Erdos85
