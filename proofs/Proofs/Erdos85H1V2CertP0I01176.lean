import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1176
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=464 profileIndexed=true rawInventoryTable=true
    orbit=c411aaa072b51add
    compact_lrat_sha256=3c737c6de9224e975e482d4ea153347f04661c6578cac3085b5dec860a97a880
    raw_lrat_sha256=36ea8d3209959c3c76e055818ba62b2787b3ffd7722c3bc84d21c3155a0b32f0
    cnf_sha256=ce0346a8e7e7803c5ae14b4696873212dad73f5d45da2c6a25cfc5a057d3be61
    binary_lrat_sha256=29393281953f5249dd18246caba97d6ebea9bf57dd9c21697b0ac0a6d90b8159
    lz4_frame_sha256=bfdba18401f87c799e5f111ac9d75d37744a36a03ba03c1757950595c4ed6a2b
    packed_lz4_sha256=bc329b6bb08a893a5edaff97e5d4a4d028a3172a9bfa347cc27fd92727581d34
    compact_bytes=1663219904 binary_bytes=731441337
    lz4_frame_bytes=430369563 packed_lz4_bytes=491850930
    source_cnf_clauses=613244 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01176Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1176, by native_decide⟩

private def h1V2P0I01176ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bc/bc329b6bb08a893a5edaff97e5d4a4d028a3172a9bfa347cc27fd92727581d34.lrat.lz4p7"

private def h1V2P0I01176RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01176ProofText
    430369563 731441337

private def h1V2P0I01176Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01176Table)
    h1V2P0I01176RawProof).toOption.get!

private theorem h1V2P0I01176Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01176Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01176Table).clauses.toList.all
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
private theorem h1V2P0I01176Check :
    LRAT.check h1V2P0I01176Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01176Table)
        h1V2P0I01176RawProof) := by
  native_decide

theorem h1V2P0I01176Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01176Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01176Nonzero
    h1V2P0I01176RawProof h1V2P0I01176Proof h1V2P0I01176Check

def h1V2P0I01176Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01176Table
  checked := h1V2P0I01176Checked

end Erdos85
