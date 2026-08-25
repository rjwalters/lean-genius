import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=741
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=296 profileIndexed=true rawInventoryTable=true
    orbit=7cf654d3ff0883b0
    compact_lrat_sha256=b8d5c0a4f420543d2428fe2a7d141ff4d34433403dce8775ff79c29f533fd677
    raw_lrat_sha256=7e41f3da6f706bf67fa21f3085a4f98a896e9b4bc853a8ab53453e400b20937d
    cnf_sha256=19b247534f0ab954e37e133f974dfae4a0a06e1d87ceb449fc967f2f6f0aa1cc
    binary_lrat_sha256=477b733540edaa72ee5dd1a5a2441ed57818ac0a7287476f71b008605b8de7ad
    lz4_frame_sha256=13267268ade1908709b3dfd65d2be4cd9f18dac9191f873d05176d282073b8d9
    packed_lz4_sha256=0cd612929d9e867e5a28fd33031140a07eae332eec049ef4c0d966faaccdc7a8
    compact_bytes=1441029180 binary_bytes=637032719
    lz4_frame_bytes=358063376 packed_lz4_bytes=409215287
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00741Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨741, by native_decide⟩

private def h1V2P0I00741ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/0c/0cd612929d9e867e5a28fd33031140a07eae332eec049ef4c0d966faaccdc7a8.lrat.lz4p7"

private def h1V2P0I00741RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00741ProofText
    358063376 637032719

private def h1V2P0I00741Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00741Table)
    h1V2P0I00741RawProof).toOption.get!

private theorem h1V2P0I00741Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00741Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00741Table).clauses.toList.all
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
private theorem h1V2P0I00741Check :
    LRAT.check h1V2P0I00741Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00741Table)
        h1V2P0I00741RawProof) := by
  native_decide

theorem h1V2P0I00741Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00741Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00741Nonzero
    h1V2P0I00741RawProof h1V2P0I00741Proof h1V2P0I00741Check

def h1V2P0I00741Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00741Table
  checked := h1V2P0I00741Checked

end Erdos85
