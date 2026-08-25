import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=329
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=139 profileIndexed=true rawInventoryTable=true
    orbit=35e3246ce0973db4
    compact_lrat_sha256=a82726f1e181c6ba9edcc57080040250f0585caff22c6b04d9834ffa5d45ee92
    raw_lrat_sha256=3f9449311d720b53d37d22e38c122e0df92d430b93fa2354bc5c20a9744cdcd8
    cnf_sha256=7ee60d990d842c14efe050778cda61416b3ef0db3b4c9ef4fbbcf40c2a30d6c0
    binary_lrat_sha256=a5d766c5469fe2064796a2c56c16db79ca59f9120023185905df809e0cba0165
    lz4_frame_sha256=19f6399e754a0c6a353d183f33d3d4c17fe54378643e75e231e0f951e0f66712
    packed_lz4_sha256=a24185180fc8d62a7f46418e487bedcb1d356cba1d8da61c40c2e973f7256433
    compact_bytes=1694364136 binary_bytes=747637293
    lz4_frame_bytes=433534717 packed_lz4_bytes=495468248
    source_cnf_clauses=613252 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00329Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨329, by native_decide⟩

private def h1V2P0I00329ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/a2/a24185180fc8d62a7f46418e487bedcb1d356cba1d8da61c40c2e973f7256433.lrat.lz4p7"

private def h1V2P0I00329RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00329ProofText
    433534717 747637293

private def h1V2P0I00329Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00329Table)
    h1V2P0I00329RawProof).toOption.get!

private theorem h1V2P0I00329Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00329Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00329Table).clauses.toList.all
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
private theorem h1V2P0I00329Check :
    LRAT.check h1V2P0I00329Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00329Table)
        h1V2P0I00329RawProof) := by
  native_decide

theorem h1V2P0I00329Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00329Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00329Nonzero
    h1V2P0I00329RawProof h1V2P0I00329Proof h1V2P0I00329Check

def h1V2P0I00329Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00329Table
  checked := h1V2P0I00329Checked

end Erdos85
