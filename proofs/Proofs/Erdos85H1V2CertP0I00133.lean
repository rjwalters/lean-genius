import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=133
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=62 profileIndexed=true rawInventoryTable=true
    orbit=147eb2ec284e907c
    compact_lrat_sha256=a45304b0d0539a672177a445a13e35fd21f97062c40d8ed6a1338f45a2f1dc5c
    raw_lrat_sha256=5db4e837328d46d084e8728349e50282c7a84ff8d3b8220df09bf0f537e03f97
    cnf_sha256=284fcb897c095df45e8d4353f572c1c0d85307bc64b55dd307d953a9127d8e36
    binary_lrat_sha256=81c1ab5de6b429e711d8985fad4a7574f0a2f540f93703a3495d3a77a7a03577
    lz4_frame_sha256=ee76645f0b66352eda5ac8464024e39b234f2f5ee3b2fdbeaec5b862e4a48c46
    packed_lz4_sha256=e561100c2318188f5276a2e51f808fa7945d872aa73efda1512d15827e873cf2
    compact_bytes=2391646068 binary_bytes=1055862072
    lz4_frame_bytes=632277190 packed_lz4_bytes=722602503
    source_cnf_clauses=613220 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00133Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨133, by native_decide⟩

private def h1V2P0I00133ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/e5/e561100c2318188f5276a2e51f808fa7945d872aa73efda1512d15827e873cf2.lrat.lz4p7"

private def h1V2P0I00133RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00133ProofText
    632277190 1055862072

private def h1V2P0I00133Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00133Table)
    h1V2P0I00133RawProof).toOption.get!

private theorem h1V2P0I00133Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00133Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00133Table).clauses.toList.all
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
private theorem h1V2P0I00133Check :
    LRAT.check h1V2P0I00133Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00133Table)
        h1V2P0I00133RawProof) := by
  native_decide

theorem h1V2P0I00133Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00133Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00133Nonzero
    h1V2P0I00133RawProof h1V2P0I00133Proof h1V2P0I00133Check

def h1V2P0I00133Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00133Table
  checked := h1V2P0I00133Checked

end Erdos85
