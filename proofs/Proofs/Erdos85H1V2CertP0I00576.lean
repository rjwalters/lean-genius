import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=576
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=222 profileIndexed=true rawInventoryTable=true
    orbit=61ef351f6b98c3c9
    compact_lrat_sha256=3fbfe73f29c6246d74b66016b6ce4a41879a8f5d048e320fa2a04776d352cbd7
    raw_lrat_sha256=02645c39f7050a410fd54fcd0d591ab9625220300347295827efe5d80b6d1600
    cnf_sha256=f4d01ebf35201facefb4346440e3f5219539eabe13f88f0b57c682ad9d9e678e
    binary_lrat_sha256=c5615f3b76d05bdf72758d90195dd4b21156a635505308f8d2bf392345dcd8cb
    lz4_frame_sha256=70b6a8686951225b01bfa40476751384d737b9faa2121d1ccbfebc1357e28f3e
    packed_lz4_sha256=33cd81f0def3b3f1e8863096040bdff938f3322d902225382b2856267dadaf62
    compact_bytes=560970824 binary_bytes=247759141
    lz4_frame_bytes=143100626 packed_lz4_bytes=163543573
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00576Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨576, by native_decide⟩

private def h1V2P0I00576ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/33/33cd81f0def3b3f1e8863096040bdff938f3322d902225382b2856267dadaf62.lrat.lz4p7"

private def h1V2P0I00576RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00576ProofText
    143100626 247759141

private def h1V2P0I00576Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00576Table)
    h1V2P0I00576RawProof).toOption.get!

private theorem h1V2P0I00576Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00576Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00576Table).clauses.toList.all
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
private theorem h1V2P0I00576Check :
    LRAT.check h1V2P0I00576Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00576Table)
        h1V2P0I00576RawProof) := by
  native_decide

theorem h1V2P0I00576Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00576Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00576Nonzero
    h1V2P0I00576RawProof h1V2P0I00576Proof h1V2P0I00576Check

def h1V2P0I00576Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00576Table
  checked := h1V2P0I00576Checked

end Erdos85
