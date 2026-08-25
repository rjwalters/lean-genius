import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=1019
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=402 profileIndexed=true rawInventoryTable=true
    orbit=ac7167e310fe007b
    compact_lrat_sha256=470d59825ab4dfb8ba16d28daaa8fa726bea9aedb43d0844f44a1741181b6e9f
    raw_lrat_sha256=b442f4c452588d6f4ebadda1583a1f0dcd6188b3dcaec968e97be3e7ff61837f
    cnf_sha256=5f6e97fa7890380b0c0f19ca003bd56c0b24583c861c742b2ef7cb34cef5f0ec
    binary_lrat_sha256=7bd5903ae29a916c1308bba3e468322be706196cdcb0a36ada0c14c0eef829f7
    lz4_frame_sha256=3c31ec302db3620751bc6bb7745d3c8a4010c00014ce438a49458c457947df90
    packed_lz4_sha256=0312d0fd8d376cf6e906f50fa16b83efc3351f1d012297640c9f5a41bc22199f
    compact_bytes=1485013403 binary_bytes=652476337
    lz4_frame_bytes=358155296 packed_lz4_bytes=409320339
    source_cnf_clauses=612996 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I01019Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨1019, by native_decide⟩

private def h1V2P0I01019ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/03/0312d0fd8d376cf6e906f50fa16b83efc3351f1d012297640c9f5a41bc22199f.lrat.lz4p7"

private def h1V2P0I01019RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I01019ProofText
    358155296 652476337

private def h1V2P0I01019Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I01019Table)
    h1V2P0I01019RawProof).toOption.get!

private theorem h1V2P0I01019Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I01019Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I01019Table).clauses.toList.all
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
private theorem h1V2P0I01019Check :
    LRAT.check h1V2P0I01019Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I01019Table)
        h1V2P0I01019RawProof) := by
  native_decide

theorem h1V2P0I01019Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I01019Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I01019Nonzero
    h1V2P0I01019RawProof h1V2P0I01019Proof h1V2P0I01019Check

def h1V2P0I01019Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I01019Table
  checked := h1V2P0I01019Checked

end Erdos85
