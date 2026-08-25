import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=726
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=286 profileIndexed=true rawInventoryTable=true
    orbit=7aa9b079313a0cc2
    compact_lrat_sha256=99c73f9a9fefd190a63ace365136c8a3f883061f5c8d946d5fa8ababa9df241d
    raw_lrat_sha256=786b647b2d4c890d1d34f1f5cf7feaee57f6934228dc8db8f54c2cd30681c93c
    cnf_sha256=c3f7e692b6752e02bc27806e0e1332ea84e7073e07526e7cb36ddd8a65f1beee
    binary_lrat_sha256=d618544c0201375821e83a62080e28b0fad4fc66a477f8a497ee4bc85ede2d8e
    lz4_frame_sha256=07c58627a2c03c20cb37e718474d1e7a11736954c990e6d82a2acff31bd1eef3
    packed_lz4_sha256=dd94eb4d0475cf92837310c419150f17bc7819f01355c3d1b48bea5031c53176
    compact_bytes=336187693 binary_bytes=147127629
    lz4_frame_bytes=85074987 packed_lz4_bytes=97228557
    source_cnf_clauses=612968 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00726Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨726, by native_decide⟩

private def h1V2P0I00726ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/dd/dd94eb4d0475cf92837310c419150f17bc7819f01355c3d1b48bea5031c53176.lrat.lz4p7"

private def h1V2P0I00726RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00726ProofText
    85074987 147127629

private def h1V2P0I00726Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00726Table)
    h1V2P0I00726RawProof).toOption.get!

private theorem h1V2P0I00726Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00726Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00726Table).clauses.toList.all
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
private theorem h1V2P0I00726Check :
    LRAT.check h1V2P0I00726Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00726Table)
        h1V2P0I00726RawProof) := by
  native_decide

theorem h1V2P0I00726Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00726Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00726Nonzero
    h1V2P0I00726RawProof h1V2P0I00726Proof h1V2P0I00726Check

def h1V2P0I00726Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00726Table
  checked := h1V2P0I00726Checked

end Erdos85
