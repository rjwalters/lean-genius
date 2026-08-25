import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=662
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=262 profileIndexed=true rawInventoryTable=true
    orbit=71d2dd21c89263f2
    compact_lrat_sha256=86d0ec94d66ef9af0e7839b7c16211dccb1bfab1f51030168db5edf2c4fdcb64
    raw_lrat_sha256=720920b4b20d71b96c0bf90573db4bc103a7a1d988b64ded6b6a56fe178baffa
    cnf_sha256=0294aad101b3eabb928a83b7bdd6703689726e842a62d64299c385676e18d599
    binary_lrat_sha256=6a02ba10159faabb54bfcba8285917345e409cbc5fcd45cf41dbde7826d7416e
    lz4_frame_sha256=0ae900b28543b080e8c9d30569af6274f9e67d448d44c3d309fa7031ce562d07
    packed_lz4_sha256=e0af73d069c4a7e41bf162ccae64f066b084effc76669ae7f2405f330628a378
    compact_bytes=1446052579 binary_bytes=642329625
    lz4_frame_bytes=362916059 packed_lz4_bytes=414761211
    source_cnf_clauses=613120 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00662Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨662, by native_decide⟩

private def h1V2P0I00662ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e0/e0af73d069c4a7e41bf162ccae64f066b084effc76669ae7f2405f330628a378.lrat.lz4p7"

private def h1V2P0I00662RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00662ProofText
    362916059 642329625

private def h1V2P0I00662Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00662Table)
    h1V2P0I00662RawProof).toOption.get!

private theorem h1V2P0I00662Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00662Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00662Table).clauses.toList.all
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
private theorem h1V2P0I00662Check :
    LRAT.check h1V2P0I00662Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00662Table)
        h1V2P0I00662RawProof) := by
  native_decide

theorem h1V2P0I00662Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00662Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00662Nonzero
    h1V2P0I00662RawProof h1V2P0I00662Proof h1V2P0I00662Check

def h1V2P0I00662Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00662Table
  checked := h1V2P0I00662Checked

end Erdos85
