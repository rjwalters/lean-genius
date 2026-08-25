import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=84
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=38 profileIndexed=true rawInventoryTable=true
    orbit=0c41c2608e5664ae
    compact_lrat_sha256=d231c647d6585633290fd758c7592950bc1f3ce736afa73728125fbf92664953
    raw_lrat_sha256=a4999ac973ef9d2fcabaef74d018b7dcf2148f1f6a4e4b0e5d3b04ba376f108b
    cnf_sha256=445e2ddd8ac1b8d7913766644c9db59c005f494635dd261ae8a090a42a4311d2
    binary_lrat_sha256=edd2d0eeb4f628e9a4560e7dcef4a27258e8054d36f76e8bf525866564c9afde
    lz4_frame_sha256=0fe178e23430dc1987870177bd7670a991f33e4576bec8baf411186845f82e4a
    packed_lz4_sha256=9acc9dcf0a5060515e8f1ab57dcc5c6cb75237443705faebca483644b8c97736
    compact_bytes=2740885813 binary_bytes=1226757105
    lz4_frame_bytes=707333049 packed_lz4_bytes=808380628
    source_cnf_clauses=613124 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00084Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨84, by native_decide⟩

private def h1V2P0I00084ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/9a/9acc9dcf0a5060515e8f1ab57dcc5c6cb75237443705faebca483644b8c97736.lrat.lz4p7"

private def h1V2P0I00084RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00084ProofText
    707333049 1226757105

private def h1V2P0I00084Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00084Table)
    h1V2P0I00084RawProof).toOption.get!

private theorem h1V2P0I00084Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00084Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00084Table).clauses.toList.all
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
private theorem h1V2P0I00084Check :
    LRAT.check h1V2P0I00084Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00084Table)
        h1V2P0I00084RawProof) := by
  native_decide

theorem h1V2P0I00084Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00084Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00084Nonzero
    h1V2P0I00084RawProof h1V2P0I00084Proof h1V2P0I00084Check

def h1V2P0I00084Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00084Table
  checked := h1V2P0I00084Checked

end Erdos85
