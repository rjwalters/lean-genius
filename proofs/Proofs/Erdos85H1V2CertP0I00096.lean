import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=96
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=44 profileIndexed=true rawInventoryTable=true
    orbit=0e6f8e3938fa2c20
    compact_lrat_sha256=cd857924b728e8062bd0d3dd385712ea9316bbcfe8843b00cc0ba76ce66c5fc4
    raw_lrat_sha256=bf7a01b58e41bca573e9def1f82ddcce6bd730aead95e272f3e54afdac688065
    cnf_sha256=8dfe2f9fd57c7f55d72f7dbb9a98a9674c902f185eda80fadc8713b947ddf77d
    binary_lrat_sha256=daf3d772b2b31fd036fa44aafc2637757b7300163b9df94878e8fa30d968070d
    lz4_frame_sha256=bc5d17beeb881634f14112683051503f47242487973965508d036ccd7cc76bfd
    packed_lz4_sha256=8ced2e97bc8c8c394137a7942e03cdd4149ec15c5f1993daaa3ea7b17ef3cafe
    compact_bytes=2457520948 binary_bytes=1088014528
    lz4_frame_bytes=648842945 packed_lz4_bytes=741534795
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00096Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨96, by native_decide⟩

private def h1V2P0I00096ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/8c/8ced2e97bc8c8c394137a7942e03cdd4149ec15c5f1993daaa3ea7b17ef3cafe.lrat.lz4p7"

private def h1V2P0I00096RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00096ProofText
    648842945 1088014528

private def h1V2P0I00096Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00096Table)
    h1V2P0I00096RawProof).toOption.get!

private theorem h1V2P0I00096Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00096Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00096Table).clauses.toList.all
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
private theorem h1V2P0I00096Check :
    LRAT.check h1V2P0I00096Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00096Table)
        h1V2P0I00096RawProof) := by
  native_decide

theorem h1V2P0I00096Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00096Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00096Nonzero
    h1V2P0I00096RawProof h1V2P0I00096Proof h1V2P0I00096Check

def h1V2P0I00096Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00096Table
  checked := h1V2P0I00096Checked

end Erdos85
