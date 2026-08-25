import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=289
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=119 profileIndexed=true rawInventoryTable=true
    orbit=2edc09646511c56b
    compact_lrat_sha256=859b452d563b33df42be5d418099cdf328be03b2122cc855f4f5efaf89cd523e
    raw_lrat_sha256=5234ae80f31239ad0a4ffeac50833b2425cfb01468e8ffc23f08b2bdf2e22477
    cnf_sha256=537da22e5cc8fae2bf1e34ce7a83c1860508db5b64c8bc32cd6c37b8f528d9a4
    binary_lrat_sha256=594b354d0bc5527709db32e1307229851509da6e55640600639aa225d7668110
    lz4_frame_sha256=c7939535d6d4c0302844a02faa4d8f17686fa512e4e26ac2e8081c56f6df65f5
    packed_lz4_sha256=bc7028f4475ea61fffc9e6d1e2a7d775e8751be20c8dabf789be0d71e6e73fea
    compact_bytes=1057537054 binary_bytes=465626792
    lz4_frame_bytes=281098729 packed_lz4_bytes=321255691
    source_cnf_clauses=613092 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00289Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨289, by native_decide⟩

private def h1V2P0I00289ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/bc/bc7028f4475ea61fffc9e6d1e2a7d775e8751be20c8dabf789be0d71e6e73fea.lrat.lz4p7"

private def h1V2P0I00289RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00289ProofText
    281098729 465626792

private def h1V2P0I00289Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00289Table)
    h1V2P0I00289RawProof).toOption.get!

private theorem h1V2P0I00289Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00289Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00289Table).clauses.toList.all
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
private theorem h1V2P0I00289Check :
    LRAT.check h1V2P0I00289Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00289Table)
        h1V2P0I00289RawProof) := by
  native_decide

theorem h1V2P0I00289Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00289Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00289Nonzero
    h1V2P0I00289RawProof h1V2P0I00289Proof h1V2P0I00289Check

def h1V2P0I00289Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00289Table
  checked := h1V2P0I00289Checked

end Erdos85
