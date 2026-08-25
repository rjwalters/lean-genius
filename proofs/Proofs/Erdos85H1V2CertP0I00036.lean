import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighV2ExtensionCertificate
import Proofs.Erdos85OrderFortyNineLratCertificateBase
import Proofs.Erdos85OneHighAllEvenCapacityInventory


/-! GENERATED exact-v2 certificate stub.
    profile=0 localIndex=36
    terminal_table=Erdos85.oneHighAllEvenCapacityInventoryTables terminalIndex=17 profileIndexed=true rawInventoryTable=true
    orbit=058ffdc7b4e84e30
    compact_lrat_sha256=af95fa230e44d5bd18aee11c48df790df02dbb89afacfff0cf2190f7b7c21a78
    raw_lrat_sha256=1435c611ed432fbf3970a541a66dcd974f9af614c658769931f9e812566c9431
    cnf_sha256=a0d5fd29f7d7916e80d318dd2ea78e3dba7146383d1119b55a44b81938b5c77d
    binary_lrat_sha256=96f4d86f7ef5f16ac728139b662b69866243b7c084e82685c156171d37157bbc
    lz4_frame_sha256=a0bd2f0908207dd8ccc0b9d495d10eb073f68a7ab868bab1ba6286ad26d55f20
    packed_lz4_sha256=cbbfde7d802a267af4ab2aa4b3847c8bc5f7b6786c256e57713010f2786da8e9
    compact_bytes=1533769669 binary_bytes=677003361
    lz4_frame_bytes=388888559 packed_lz4_bytes=444444068
    source_cnf_clauses=613140 -/

namespace Erdos85

open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
def h1V2P0I00036Table : OneHighMissTable :=
  (oneHighInventoryTables (0 : Fin 5)).get
    ⟨36, by native_decide⟩

private def h1V2P0I00036ProofText : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/cert-root/packed/cb/cbbfde7d802a267af4ab2aa4b3847c8bc5f7b6786c256e57713010f2786da8e9.lrat.lz4p7"

private def h1V2P0I00036RawProof : Array LRAT.IntAction :=
  parsePackedLz4OrderFortyNineLratProof h1V2P0I00036ProofText
    388888559 677003361

private def h1V2P0I00036Proof : Array LRAT.IntAction :=
  (prepareLratProof
    (oneHighFamilyV2SatCnf 0 h1V2P0I00036Table)
    h1V2P0I00036RawProof).toOption.get!

private theorem h1V2P0I00036Nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0 h1V2P0I00036Table).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 h1V2P0I00036Table).clauses.toList.all
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
private theorem h1V2P0I00036Check :
    LRAT.check h1V2P0I00036Proof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf 0 h1V2P0I00036Table)
        h1V2P0I00036RawProof) := by
  native_decide

theorem h1V2P0I00036Checked :
    OneHighFamilyV2CheckedUnsat 0 h1V2P0I00036Table :=
  oneHighFamilyV2CheckedUnsat_of_extension_lrat h1V2P0I00036Nonzero
    h1V2P0I00036RawProof h1V2P0I00036Proof h1V2P0I00036Check

def h1V2P0I00036Entry : OneHighFamilyV2CheckedEntry 0 where
  table := h1V2P0I00036Table
  checked := h1V2P0I00036Checked

end Erdos85
