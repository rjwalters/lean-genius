import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=752
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=302 profileIndexed=true rawInventoryTable=true
    orbit=803a06900c3ac1ed
    compact_lrat_sha256=ecfee66c0edd25f42149ef9908192f753115dc867a48900ed8863cba179bc46b
    raw_lrat_sha256=101db0020d927f9de856c754b61c3550ec7d0254fdb9254522672d7211fc2cb9
    cnf_sha256=f2511e6798edfd3cfdd57f423c363cecb51e7c4d35d3502f7ac1b45467391678
    binary_lrat_sha256=3dbc59eface1996bc0172a8045ba6903bb8538d0808b9fe6822afc73f4bc9977
    lz4_frame_sha256=32a0ff570f3fb1c0374d9b15bafd80bdc9b754a69d962dc5ef73877d5025f211
    packed_lz4_sha256=d99e0fc8e0a8fe0d85d95e5226cda5bd3f654478a3a673c6bab80b738ca74d92
    compact_bytes=96407861 binary_bytes=42121615
    lz4_frame_bytes=22693862 packed_lz4_bytes=25935843
    source_cnf_clauses=613056 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00752Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨752, by native_decide⟩

private def h1V2P0I00752ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/d9/d99e0fc8e0a8fe0d85d95e5226cda5bd3f654478a3a673c6bab80b738ca74d92.lrat.lz4p7"

private def h1V2P0I00752RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00752ProofText
    22693862 42121615

private def h1V2P0I00752Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00752Table)
    h1V2P0I00752RawProof).toOption.get!

private theorem h1V2P0I00752Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00752Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00752Table).clauses.toList.all
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
private theorem h1V2P0I00752Check :
    LRAT.check h1V2P0I00752Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00752Table)
        h1V2P0I00752RawProof) := by
  native_decide

theorem h1V2P0I00752Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00752Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00752Nonzero
    h1V2P0I00752RawProof h1V2P0I00752Proof h1V2P0I00752Check

def h1V2P0I00752Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00752Table
  checked := h1V2P0I00752Checked

end Erdos85
