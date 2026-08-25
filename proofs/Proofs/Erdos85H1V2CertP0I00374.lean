import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=374
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=157 profileIndexed=true rawInventoryTable=true
    orbit=3f9d4c8822282802
    compact_lrat_sha256=f0ef84c6e14fe5fbde31b74cf8299afcd84e0f51e3609332115126d94a34847f
    raw_lrat_sha256=0ae10722bdb6da0aa94010c50c5dfb9c439a06fb3676d57f1030d32e37d8ad1b
    cnf_sha256=641d6eb3f0084f5fee9f77407cb487b2dc825f5a33700fe68d50ffdf308b09d1
    binary_lrat_sha256=5c91860479b6a864b3126cc5e9e671579c3fe9761015e0136ad156c3f21735d9
    lz4_frame_sha256=d4e0a279e3f4e846d8520131302c3b11d12ea425c0572b50be296b84a45794b1
    packed_lz4_sha256=c7b53e0c102c11ad5cf40700ea11ff3fa165d5e934b036cd0098655cc6639e6e
    compact_bytes=1172608102 binary_bytes=517939308
    lz4_frame_bytes=305809537 packed_lz4_bytes=349496614
    source_cnf_clauses=613060 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00374Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨374, by native_decide⟩

private def h1V2P0I00374ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/c7/c7b53e0c102c11ad5cf40700ea11ff3fa165d5e934b036cd0098655cc6639e6e.lrat.lz4p7"

private def h1V2P0I00374RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00374ProofText
    305809537 517939308

private def h1V2P0I00374Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00374Table)
    h1V2P0I00374RawProof).toOption.get!

private theorem h1V2P0I00374Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00374Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00374Table).clauses.toList.all
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
private theorem h1V2P0I00374Check :
    LRAT.check h1V2P0I00374Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00374Table)
        h1V2P0I00374RawProof) := by
  native_decide

theorem h1V2P0I00374Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00374Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00374Nonzero
    h1V2P0I00374RawProof h1V2P0I00374Proof h1V2P0I00374Check

def h1V2P0I00374Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00374Table
  checked := h1V2P0I00374Checked

end Erdos85
