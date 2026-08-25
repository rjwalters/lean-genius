import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=294
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=122 profileIndexed=true rawInventoryTable=true
    orbit=2fb01233a0d6d670
    compact_lrat_sha256=c984368ae0b054cf42625a9cb01cb7b292aca1aa34228a302374742ec7f2cf45
    raw_lrat_sha256=f7e0251d65b10b0a604924c5467c5e7de8a61c71ac2fd71d3d190e830c5b8c04
    cnf_sha256=de9bdc721fbe9c803274f7f095f725b3bb95bfe093c2ece199292f1b079890f1
    binary_lrat_sha256=323b904fd34eb67fc071cd096a47f7294e687e9f48558f5f5135e0f8096a7d04
    lz4_frame_sha256=d9589b6e0ca5d5a471721a0e8e2465ab65b46698167597388180dbed8ee66d7e
    packed_lz4_sha256=efba227a19db2fa24e526d5a0e44c28771900ae0abb3f7795650864bcc57ed58
    compact_bytes=997740730 binary_bytes=439162494
    lz4_frame_bytes=269720688 packed_lz4_bytes=308252215
    source_cnf_clauses=613240 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00294Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨294, by native_decide⟩

private def h1V2P0I00294ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/ef/efba227a19db2fa24e526d5a0e44c28771900ae0abb3f7795650864bcc57ed58.lrat.lz4p7"

private def h1V2P0I00294RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00294ProofText
    269720688 439162494

private def h1V2P0I00294Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00294Table)
    h1V2P0I00294RawProof).toOption.get!

private theorem h1V2P0I00294Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00294Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00294Table).clauses.toList.all
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
private theorem h1V2P0I00294Check :
    LRAT.check h1V2P0I00294Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00294Table)
        h1V2P0I00294RawProof) := by
  native_decide

theorem h1V2P0I00294Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00294Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00294Nonzero
    h1V2P0I00294RawProof h1V2P0I00294Proof h1V2P0I00294Check

def h1V2P0I00294Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00294Table
  checked := h1V2P0I00294Checked

end Erdos85
