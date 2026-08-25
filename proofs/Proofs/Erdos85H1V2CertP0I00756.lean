import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=756
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=304 profileIndexed=true rawInventoryTable=true
    orbit=80681b85009b8613
    compact_lrat_sha256=a32be7085d76a7820bbcbb92da361eb82385edcbad6f5817e1c0474487175c8b
    raw_lrat_sha256=1e825eed63e3f8107ecb0b3a845a506c3ba615480dab531c1c8561ab125cf6b3
    cnf_sha256=9e1a89392981adc4c477a19bbdafcff5ae4c2a62eae85cce9b9aa78983358a66
    binary_lrat_sha256=f037429c2d3c609bc0d11afdaad576d1eb6f6550e3138b8d6f97c8aea6c1c3d7
    lz4_frame_sha256=bc92ae7ba33bf5baf6e912b734b7c3f70a443f8fb41eca85f3bb71328db02f0c
    packed_lz4_sha256=f5e2ebd5cb85ed6bf8b7d2952dc45e8f56d14fc61b83feb227b53e46c330e6c5
    compact_bytes=1521390560 binary_bytes=672596753
    lz4_frame_bytes=405937605 packed_lz4_bytes=463928692
    source_cnf_clauses=613154 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00756Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨756, by native_decide⟩

private def h1V2P0I00756ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/f5/f5e2ebd5cb85ed6bf8b7d2952dc45e8f56d14fc61b83feb227b53e46c330e6c5.lrat.lz4p7"

private def h1V2P0I00756RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00756ProofText
    405937605 672596753

private def h1V2P0I00756Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00756Table)
    h1V2P0I00756RawProof).toOption.get!

private theorem h1V2P0I00756Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00756Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00756Table).clauses.toList.all
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
private theorem h1V2P0I00756Check :
    LRAT.check h1V2P0I00756Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00756Table)
        h1V2P0I00756RawProof) := by
  native_decide

theorem h1V2P0I00756Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00756Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00756Nonzero
    h1V2P0I00756RawProof h1V2P0I00756Proof h1V2P0I00756Check

def h1V2P0I00756Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00756Table
  checked := h1V2P0I00756Checked

end Erdos85
