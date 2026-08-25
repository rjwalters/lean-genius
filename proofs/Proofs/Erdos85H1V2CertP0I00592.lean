import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=592
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=229 profileIndexed=true rawInventoryTable=true
    orbit=64ad5d71530a74cb
    compact_lrat_sha256=7467ef43bcfca29de9afe2353e984103b286c27dcba7d7d07c2e4780da600df4
    raw_lrat_sha256=ea0cbe1b28aaabcbdacb7cbe4fac7c6e4c6eb8d0fc5a06e0ef6ff689eafeca20
    cnf_sha256=2fbe92ef69c34c8a3644c6d38b87b9529b36c161573c477a69fdc71b654f41ac
    binary_lrat_sha256=c5161a2975e5c0fd3e5ca4c6920c1d4ea3cdb70750349f75396689dee6227ce2
    lz4_frame_sha256=e552143153191c292d5b5313d8afa66613f3b62d3accfbcf5b454cd95dccc63b
    packed_lz4_sha256=7255c283f8db361eec86172df48c2328af7e643b3e501e54ab63776d47ef1e94
    compact_bytes=1488155644 binary_bytes=663133190
    lz4_frame_bytes=395525190 packed_lz4_bytes=452028789
    source_cnf_clauses=613084 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00592Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨592, by native_decide⟩

private def h1V2P0I00592ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/72/7255c283f8db361eec86172df48c2328af7e643b3e501e54ab63776d47ef1e94.lrat.lz4p7"

private def h1V2P0I00592RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00592ProofText
    395525190 663133190

private def h1V2P0I00592Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00592Table)
    h1V2P0I00592RawProof).toOption.get!

private theorem h1V2P0I00592Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00592Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00592Table).clauses.toList.all
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
private theorem h1V2P0I00592Check :
    LRAT.check h1V2P0I00592Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00592Table)
        h1V2P0I00592RawProof) := by
  native_decide

theorem h1V2P0I00592Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00592Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00592Nonzero
    h1V2P0I00592RawProof h1V2P0I00592Proof h1V2P0I00592Check

def h1V2P0I00592Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00592Table
  checked := h1V2P0I00592Checked

end Erdos85
