import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=855
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=339 profileIndexed=true rawInventoryTable=true
    orbit=902288239786f6c8
    compact_lrat_sha256=ce2f7bf238f4bdecb35d54d2403cd4e94996e0b89347d15e62bdc8d9918669de
    raw_lrat_sha256=aab2edc61d9ac1d1782b6a357902917c0053bd1ac39d3c8051dab522ed975bf2
    cnf_sha256=edc86acfeb2e0de0138a2fb0d9cc0b5fcbc4ac7d7002853c340041fed33ba4a0
    binary_lrat_sha256=2959c9124557dc02e962df884215cc7e3b313a18ec1e6a6fc9f74f0319db8103
    lz4_frame_sha256=a3ac50326916bbf4f12efcf83557768f55094d11986b09fe33efef3651fa1548
    packed_lz4_sha256=24987cc0ee100d966c4aca860aae5189f7bfd52c87a9c604a1d9b9a7d9bd99bc
    compact_bytes=1535238751 binary_bytes=675427769
    lz4_frame_bytes=386169032 packed_lz4_bytes=441336037
    source_cnf_clauses=613196 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00855Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨855, by native_decide⟩

private def h1V2P0I00855ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/24/24987cc0ee100d966c4aca860aae5189f7bfd52c87a9c604a1d9b9a7d9bd99bc.lrat.lz4p7"

private def h1V2P0I00855RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00855ProofText
    386169032 675427769

private def h1V2P0I00855Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00855Table)
    h1V2P0I00855RawProof).toOption.get!

private theorem h1V2P0I00855Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00855Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00855Table).clauses.toList.all
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
private theorem h1V2P0I00855Check :
    LRAT.check h1V2P0I00855Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00855Table)
        h1V2P0I00855RawProof) := by
  native_decide

theorem h1V2P0I00855Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00855Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00855Nonzero
    h1V2P0I00855RawProof h1V2P0I00855Proof h1V2P0I00855Check

def h1V2P0I00855Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00855Table
  checked := h1V2P0I00855Checked

end Erdos85
