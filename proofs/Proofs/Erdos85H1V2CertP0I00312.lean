import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=312
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=131 profileIndexed=true rawInventoryTable=true
    orbit=33a1e538a4ccb993
    compact_lrat_sha256=51dec6b20b7087ec9839a5655be97dc52d5f5003582edd427d061a9d03b80a7b
    raw_lrat_sha256=8cd1d7f859ac60bbf4eeeb290801dc896ee5b0be0f8448c8ac0499147d2e2ffd
    cnf_sha256=a13270a498502cb5a1d386dc7bd898022d90aa8e2000f5e7e72ac35727f94031
    binary_lrat_sha256=e1243ea7a9de2392f8f8f579865369e68b8e1574f11ffdf0c041ba4fa1679916
    lz4_frame_sha256=c516789fe9528775acb4dbf0577a6b4ebaf2d82e41cb22736a46c84d99329703
    packed_lz4_sha256=ebd69ceb1ad7bd5323ade6a282fdc46c72e62e60fe1ad168c0fb5f2949b9f20c
    compact_bytes=1834878900 binary_bytes=808715477
    lz4_frame_bytes=483721613 packed_lz4_bytes=552824701
    source_cnf_clauses=613240 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00312Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨312, by native_decide⟩

private def h1V2P0I00312ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/eb/ebd69ceb1ad7bd5323ade6a282fdc46c72e62e60fe1ad168c0fb5f2949b9f20c.lrat.lz4p7"

private def h1V2P0I00312RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00312ProofText
    483721613 808715477

private def h1V2P0I00312Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00312Table)
    h1V2P0I00312RawProof).toOption.get!

private theorem h1V2P0I00312Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00312Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00312Table).clauses.toList.all
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
private theorem h1V2P0I00312Check :
    LRAT.check h1V2P0I00312Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00312Table)
        h1V2P0I00312RawProof) := by
  native_decide

theorem h1V2P0I00312Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00312Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00312Nonzero
    h1V2P0I00312RawProof h1V2P0I00312Proof h1V2P0I00312Check

def h1V2P0I00312Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00312Table
  checked := h1V2P0I00312Checked

end Erdos85
