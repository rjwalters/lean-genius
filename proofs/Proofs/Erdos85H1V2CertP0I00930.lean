import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=930
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=370 profileIndexed=true rawInventoryTable=true
    orbit=9c89c4718e463e27
    compact_lrat_sha256=1fc418524e130631c0ac576ff66d3701899e09dc03e49250d38038f1a4e57941
    raw_lrat_sha256=94944b626e5b0de42b73bfbb1ffb01ac8969677848a204189cbce20c482d9b84
    cnf_sha256=bab5ece6d0cd7bbaf66d46a07aeca6ec3a661eff24f9201281182d3aa64946a1
    binary_lrat_sha256=9c7c5f2ded6619ade401b12f41a02889f160b9972a6fbef07da00b9ce10f1d9f
    lz4_frame_sha256=18b5c1799c568af450759a4eb912bd50fccb9919f43ea67e49112ba5aac023d7
    packed_lz4_sha256=45f355d4147638c768a5afc503805ba190168c9669655c4453690e6f63d99e17
    compact_bytes=1469856501 binary_bytes=652530973
    lz4_frame_bytes=398233175 packed_lz4_bytes=455123629
    source_cnf_clauses=613236 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00930Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨930, by native_decide⟩

private def h1V2P0I00930ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/45/45f355d4147638c768a5afc503805ba190168c9669655c4453690e6f63d99e17.lrat.lz4p7"

private def h1V2P0I00930RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00930ProofText
    398233175 652530973

private def h1V2P0I00930Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00930Table)
    h1V2P0I00930RawProof).toOption.get!

private theorem h1V2P0I00930Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00930Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00930Table).clauses.toList.all
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
private theorem h1V2P0I00930Check :
    LRAT.check h1V2P0I00930Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00930Table)
        h1V2P0I00930RawProof) := by
  native_decide

theorem h1V2P0I00930Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00930Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00930Nonzero
    h1V2P0I00930RawProof h1V2P0I00930Proof h1V2P0I00930Check

def h1V2P0I00930Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00930Table
  checked := h1V2P0I00930Checked

end Erdos85
